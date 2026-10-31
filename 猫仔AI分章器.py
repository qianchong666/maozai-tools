#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""猫仔AI分章器 v1.1 —— 结构体检 · 三种切分模式

流程：正则族全量扫全书取标题候选（不看缩进）→ 结构证据（章号缺号）自动补全
     → 只剩真歧义才批量交给小模型判「标题/正文」→ 按模式落盘 + 体检报告
模型只回 is_heading，正文一个字都不经它手；API 挂了只走规则，照样出章。

三种模式（界面里自己选）：
  · 分章：按「第N章」切，一章一个 txt（原来的模式）
  · 分卷：按「第N卷/部/篇/集」切，一卷一个 txt
  · 分块：先分章，再把同一卷内的章节按累计 token 贪心合并成块，
          例如限 30000 token，就取「离 30000 最近但不超」的连续若干章为一块。
          不跨卷合并：卷尾剩下的章节单独成块，下一卷从新块开始。
分章/分卷/分块 都按「卷内章号」判重号——很多书每卷从第1章重新编号，
跨卷同号是正常的，不算重号。
"""

import os
import re
import json
import time
import threading
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog

try:
    import requests
except Exception:
    requests = None

APP_TITLE = "猫仔AI分章器 v1.1"
CFG_FILE = "aichapter_config.json"
DEFAULT_CFG = {
    "enable_ai": True,
    "api_url": "http://127.0.0.1:18080/v1/chat/completions",
    "api_key": "",
    "model": "Qwen3.5-4B-UD-Q8_K_XL",
    "timeout": 600,
    "max_retries": 3,
    "v5_long_block_chars": 40000,
    "v5_dup_policy": "修订版",
    "v5_batch": 20,
    "v5_toc_gap": 2,
    "mode": "chapter",
    "v6_chunk_tokens": 30000,
    "v6_keep_chapter_files": True,
    "last_out": "",
}

MODE_NAMES = {
    "chapter": "分章（按章节切）",
    "volume": "分卷（按第N卷/部/篇/集 切）",
    "chunk": "分块（分章后按累计 token 合并成块）",
}

def cfg_path():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), CFG_FILE)

def load_cfg():
    cfg = dict(DEFAULT_CFG)
    p = cfg_path()
    if os.path.exists(p):
        try:
            cfg.update(json.load(open(p, encoding="utf-8")) or {})
        except Exception:
            pass
    return cfg

def save_cfg(cfg):
    try:
        json.dump(cfg, open(cfg_path(), "w", encoding="utf-8"), indent=2, ensure_ascii=False)
    except Exception:
        pass

def read_text_any(file_path):
    for enc in ("utf-8-sig", "utf-8", "gbk", "gb18030", "shift_jis", "utf-16", "latin1"):
        try:
            with open(file_path, "r", encoding=enc) as f:
                return f.read()
        except (UnicodeDecodeError, UnicodeError):
            continue
    raise ValueError("无法用任何支持的编码读取文件")

def sanitize_filename(s):
    return "".join(c for c in str(s) if c.isalnum() or c in " _-").rstrip() or "untitled"

def pretty_model_name(n):
    """端点返回的模型名如果是一整条路径（llama.cpp 默认如此），裁成干净的文件名。"""
    s = str(n or "").strip()
    if not s:
        return s
    if os.sep in s or "/" in s or s.lower().endswith(".gguf"):
        base = os.path.basename(s.replace("\\", "/"))
        if base.lower().endswith(".gguf"):
            base = base[:-5]
        return base or s
    return s

def normalize_api_url(u):
    """把随手填的地址补成完整的 chat/completions 端点。"""
    u = str(u or "").strip().rstrip("/")
    if not u:
        return u
    if u.endswith("/chat/completions"):
        return u
    if u.endswith("/v1"):
        return u + "/chat/completions"
    return u + "/v1/chat/completions"


# ==================== 模式 E 核心（原样搬过来） ====================
# ================== 模式 E：结构体检分章（v5）==================
# 顺序是：正则族全量扫全书取标题候选（不看缩进）→ 结构证据（缺号）先补全 → 只剩真歧义
# 才批量交给小模型判「标题 / 正文」→ 逐章落盘 + 出一份体检报告。
# 模型只回 is_heading，正文一个字都不经它手；API 挂了只走规则，照样出结果。

V5_CN_DIGIT = {"零": 0, "〇": 0, "一": 1, "二": 2, "两": 2, "三": 3, "四": 4,
               "五": 5, "六": 6, "七": 7, "八": 8, "九": 9}
V5_CN_UNIT = {"十": 10, "百": 100, "千": 1000, "万": 10000}

V5_HEAD_CH = re.compile(r"^第\s*([0-9零〇一二两三四五六七八九十百千万]{1,9})\s*([章节回])")
V5_HEAD_VOL = re.compile(r"^第\s*([0-9零〇一二两三四五六七八九十百千万]{1,9})\s*([卷部篇集])")
V5_HEAD_EXTRA = re.compile(r"^(序章|序言|序|楔子|引子|前言|尾声|终章|后记|番外|大结局|结局|附录)")
V5_INLINE = re.compile(r"第\s*[0-9零〇一二两三四五六七八九十百千万]{1,9}\s*[章节回卷部篇集]")
# 这些标点结尾说明是句子，不是标题
V5_SENT_END = ("。", "！", "？", "，", "…", "；", "：", "”", "')")


def v5_cn_to_int(s):
    """中文/阿拉伯章节号 → int；解析不了给 None。"""
    s = (s or "").strip()
    if not s:
        return None
    if s.isdigit():
        return int(s)
    total = section = num = 0
    for ch in s:
        if ch in V5_CN_DIGIT:
            num = V5_CN_DIGIT[ch]
        elif ch in V5_CN_UNIT:
            u = V5_CN_UNIT[ch]
            if u == 10000:
                total += (section + num) * 10000
                section = num = 0
            else:
                section += (num if num else 1) * u
                num = 0
        else:
            return None
    return total + section + num


def v5_scan(text):
    """扫全书 → (lines, 确定标题, 歧义候选)。不依赖缩进，也接受带缩进的标题。"""
    lines = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    heads, amb = [], []
    for i, raw in enumerate(lines):
        s = raw.strip()
        if not s:
            continue
        kind, unit, num = None, "", None
        m = V5_HEAD_CH.match(s)
        if m:
            kind, unit, num = "chapter", m.group(2), v5_cn_to_int(m.group(1))
        else:
            m = V5_HEAD_VOL.match(s)
            if m:
                kind, unit, num = "volume", m.group(2), v5_cn_to_int(m.group(1))
            else:
                m = V5_HEAD_EXTRA.match(s)
                if m:
                    kind, unit = "extra", m.group(1)
        indented = bool(raw) and raw[0].isspace()
        if kind and len(s) <= 80:
            rec = {"line": i + 1, "raw": s, "kind": kind, "unit": unit, "num": num,
                   "indented": indented}
            if indented or len(s) > 30 or s.endswith(V5_SENT_END):
                rec["why"] = ("标题带缩进" if indented else
                              ("标题过长" if len(s) > 30 else "像句子"))
                amb.append(rec)
            else:
                heads.append(rec)
        elif V5_INLINE.search(s[:16]):
            amb.append({"line": i + 1, "raw": s[:100], "kind": None, "unit": "", "num": None,
                        "indented": indented, "why": "正文里出现章节样式"})
    return lines, heads, amb


def v5_promote_by_structure(heads, amb):
    """结构/形态证据能定的先定掉，剩下的才花模型调用。
    返回 (提升的标题, 真正留给模型的候选)。"""
    have = {h["num"] for h in heads if h["kind"] == "chapter" and h["num"] is not None}
    promoted, left = [], []
    for c in amb:
        s = str(c["raw"])
        looks_like_title = (c["why"] == "标题带缩进" and len(s) <= 40
                            and not s.endswith(V5_SENT_END))
        fills_gap = (c["kind"] == "chapter" and c["num"] is not None
                     and c["num"] not in have and len(s) <= 30)
        if looks_like_title or fills_gap:
            c = dict(c, promoted_by="形态" if looks_like_title else "缺号")
            promoted.append(c)
            if c["kind"] == "chapter" and c["num"] is not None:
                have.add(c["num"])
        else:
            left.append(c)
    return promoted, left


class V5JudgeClient:
    """只判一件事：这批候选行里哪些是真标题。从不输出正文。"""

    def __init__(self, cfg, post=None):
        if requests is None:
            raise RuntimeError("缺少 requests：在 .venv 里 pip install requests")
        self.cfg = dict(cfg)
        self.requests = requests
        self.post = post

    def _headers(self):
        h = {"Content-Type": "application/json"}
        if self.cfg.get("api_key"):
            h["Authorization"] = "Bearer " + str(self.cfg["api_key"]).strip()
        return h

    """只判一件事：这批候选行里哪些是真标题。从不输出正文。"""

    SYSTEM = ("你是中文小说结构校验器。给定若干候选行及各自的上一行末尾、下一行开头，"
              "判断该候选行是真正的章节标题(heading)，还是正文里顺带提到的句段(body)。"
              "目录页条目算 heading。绝不改写、复述或输出正文，只输出要求的 JSON。")

    def judge(self, cases):
        """cases: [{idx, prev, line, nxt}]；返回 ({idx: (bool, kind)}, 错误)。"""
        blocks = []
        for c in cases:
            blocks.append(f"[{c['idx']}] 上一行末尾：…{c['prev'][-40:]}\n"
                          f"     候选行：{c['line']}\n"
                          f"     下一行开头：{c['nxt'][:40]}…")
        prompt = ("逐个判断下列候选行：\n" + "\n".join(blocks) +
                  f'\n\n只输出一行 JSON：{{"items":[{{"idx":1,"is_heading":true,"kind":"chapter"}}]}}，'
                  'kind 取值 chapter/special/volume/toc/body；每个候选都要有一条。')
        for k in range(max(1, int(self.cfg.get("max_retries", 3) or 1))):
            try:
                body = {"model": self.cfg.get("model"), "temperature": 0,
                        "max_tokens": 60 + 45 * len(cases),
                        "chat_template_kwargs": {"enable_thinking": False},
                        "messages": [{"role": "system", "content": self.SYSTEM},
                                     {"role": "user", "content": prompt}]}
                r = self.requests.post(self.cfg["api_url"], json=body,
                                       timeout=float(self.cfg.get("timeout", 600)),
                                       headers=self._headers())
                content = ((r.json().get("choices") or [{}])[0].get("message") or {}).get("content") or ""
                out = self._parse(content)
                if out:
                    return out, None
            except Exception as e:
                last = f"{type(e).__name__}: {e}"
            time.sleep(0.8 * (k + 1))
        return {}, locals().get("last", "模型未给出可用答复")

    @staticmethod
    def _parse(content):
        out = {}
        m = re.search(r"\[.*\]", content, re.S)
        if m:
            try:
                for it in json.loads(m.group(0)):
                    if isinstance(it, dict) and "idx" in it:
                        out[int(it["idx"])] = (bool(it.get("is_heading")), str(it.get("kind", "?")))
            except Exception:
                pass
        if not out:
            m = re.search(r"\{.*\}", content, re.S)
            if m:
                try:
                    for it in json.loads(m.group(0)).get("items", []):
                        out[int(it["idx"])] = (bool(it.get("is_heading")), str(it.get("kind", "?")))
                except Exception:
                    pass
        return out


def v5_finalize(lines, heads, dup_policy="修订版", long_chars=40000, toc_gap=2):
    """把标题排成章节，算块长/连续性/重号/目录页/超长块。"""
    heads = sorted(heads, key=lambda h: h["line"])
    segs = []
    for k, h in enumerate(heads):
        end = heads[k + 1]["line"] - 1 if k + 1 < len(heads) else len(lines)
        segs.append({"line": h["line"], "raw": h["raw"], "kind": h["kind"], "num": h["num"],
                     "unit": h["unit"], "indented": h.get("indented", False),
                     "promoted_by": h.get("promoted_by", ""),
                     "end": end, "chars": sum(len(x.strip()) for x in lines[h["line"]:end])})
    # 目录页：连续 >=3 条标题之间几乎没有正文
    toc = []
    run = [0]
    for k in range(1, len(segs)):
        if segs[k]["line"] - segs[k - 1]["line"] <= toc_gap:
            run.append(k)
        else:
            if len(run) >= 3:
                toc.append((segs[run[0]]["line"], segs[run[-1]]["line"], len(run)))
            run = [k]
    if len(run) >= 3:
        toc.append((segs[run[0]]["line"], segs[run[-1]]["line"], len(run)))
    # 重号
    dups = {}
    for s in segs:
        if s["kind"] == "chapter" and s["num"] is not None:
            dups.setdefault(s["num"], []).append(s)
    dups = {n: v for n, v in dups.items() if len(v) > 1}
    # 连续性
    chap = [s for s in segs if s["kind"] == "chapter" and s["num"] is not None]
    jumps = []
    for a, b in zip(chap, chap[1:]):
        # 同号相邻＝重号（已单列），不算跳号
        if b["num"] != a["num"] + 1 and b["num"] != a["num"]:
            jumps.append((a["num"], b["num"], b["line"]))
    gaps = [n for n in range(1, (chap[-1]["num"] + 1) if chap else 1)
            if n not in {s["num"] for s in chap}]
    longs = [s for s in segs if s["chars"] > long_chars]
    return segs, {"dups": dups, "jumps": jumps, "gaps": gaps, "toc": toc,
                  "longs": longs, "indented": [s for s in segs if s["indented"]]}


# ==================== v6：token 计数 + 卷识别 ====================
_TIK = {"enc": None, "tried": False}


def _ensure_enc():
    """优先 tiktoken（cl100k_base）算真 token；没装就按字数估算。"""
    if not _TIK["tried"]:
        _TIK["tried"] = True
        try:
            import tiktoken
            _TIK["enc"] = tiktoken.get_encoding("cl100k_base")
        except Exception:
            _TIK["enc"] = None
    return _TIK["enc"]


def count_tokens(text, chars_per_token=1.6):
    enc = _ensure_enc()
    if enc is not None:
        try:
            return len(enc.encode(text))
        except Exception:
            pass
    return max(1, int(len(text) / max(0.5, float(chars_per_token or 1.6))))


def tokens_method():
    enc = _ensure_enc()
    return "tiktoken(cl100k_base)" if enc is not None else "按字数估算（1 token≈1.6 字）"


V6_VOL_HEAD = re.compile(r"^第\s*([0-9零〇一二两三四五六七八九十百千]{1,9})\s*[卷部篇集]")
V6_VOL_PRE = re.compile(r"^[卷部篇集]\s*([0-9零〇一二两三四五六七八九十百千]{1,9})")


def v6_volume_candidates(lines):
    """全量扫「第N卷/部/篇/集」「卷N」样式的行，单个候选不做判断，只收证据。"""
    out = []
    for i, raw in enumerate(lines):
        s = raw.strip()
        if not s or len(s) > 40:
            continue
        m = V6_VOL_HEAD.match(s) or V6_VOL_PRE.match(s)
        if not m:
            continue
        num = v5_cn_to_int(m.group(1))
        if not num:
            continue
        if s.endswith(V5_SENT_END):
            continue
        out.append({"line": i + 1, "raw": s, "kind": "volume", "unit": "卷", "num": num,
                    "indented": bool(raw) and raw[0].isspace(), "promoted_by": ""})
    return out


def v6_pick_volumes(heads, lines):
    """从全部标题里挑出真正的卷界限：编号必须单调递增，内容太少的“卷”不算界限。"""
    cands = [h for h in heads if h.get("kind") == "volume" and h.get("num")]
    cands = sorted({(h["line"], h["num"]): h for h in cands}.values(), key=lambda x: x["line"])
    kept, last = [], 0
    for h in cands:
        n = int(h["num"])
        if n <= last:          # 同号/回跳：正文顺带提到的“第X卷”
            continue
        kept.append(h)
        last = n
    if not kept:
        return []
    pruned = []
    for k, h in enumerate(kept):
        end = kept[k + 1]["line"] - 1 if k + 1 < len(kept) else len(lines)
        chars = sum(len(x.strip()) for x in lines[h["line"]:end])
        if chars < 200 and pruned:      # 只有标题没有内容 → 并进上一卷
            continue
        pruned.append(h)
    return pruned


def v6_volume_ranges(lines, heads):
    """卷模式用：返回 [(开篇?)各卷的行区间]。"""
    vols = v6_pick_volumes(heads, lines)
    ranges = []
    if vols:
        first = vols[0]["line"]
        pre = sum(len(x.strip()) for x in lines[:first - 1])
        if pre >= 50:
            ranges.append({"idx": 0, "title": "开篇", "start": 1, "end": first - 1,
                           "chars": pre, "num": 0})
    for k, h in enumerate(vols):
        start = h["line"]
        end = vols[k + 1]["line"] - 1 if k + 1 < len(vols) else len(lines)
        ranges.append({"idx": k + 1, "title": h["raw"], "start": start, "end": end,
                       "chars": sum(len(x.strip()) for x in lines[start - 1:end]),
                       "num": h["num"]})
    return ranges, vols


def v6_count_chapters(heads, a, b):
    return sum(1 for h in heads if h.get("kind") == "chapter" and a <= h["line"] <= b)


def v6_title_key(raw):
    """判重号用的标题指纹：去掉标点空格和「修订/版」这类版本词。"""
    s = re.sub(r"[\s\W_]+", "", str(raw or ""))
    for w in ("修订", "修改", "重写", "改稿", "定稿", "版"):
        s = s.replace(w, "")
    return s


def v6_finalize(lines, all_heads, dup_policy="修订版", long_chars=40000, toc_gap=2):
    """切段 + 卷归属 + 卷内判重号。

    卷标题本身不单独成段（它的正文几乎只有标题那一行）；它只用来给每段标卷，
    所以「第N卷」那行会留在上一章末尾，不丢字。
    """
    vols = v6_pick_volumes(all_heads, lines)
    heads = sorted([h for h in all_heads if h.get("kind") != "volume"], key=lambda h: h["line"])
    segs, vi = [], 0
    for k, h in enumerate(heads):
        end = heads[k + 1]["line"] - 1 if k + 1 < len(heads) else len(lines)
        while vi < len(vols) and vols[vi]["line"] <= h["line"]:
            vi += 1
        segs.append({"line": h["line"], "raw": h["raw"], "kind": h["kind"], "num": h["num"],
                     "unit": h.get("unit", ""), "indented": h.get("indented", False),
                     "promoted_by": h.get("promoted_by", ""), "end": end,
                     "chars": sum(len(x.strip()) for x in lines[h["line"] - 1:end]),
                     "vol": vi, "vol_title": vols[vi - 1]["raw"] if vi > 0 else ""})
    # 目录页：连续 >=3 条标题之间几乎没有正文
    toc, run = [], [0]
    for k in range(1, len(segs)):
        if segs[k]["line"] - segs[k - 1]["line"] <= toc_gap:
            run.append(k)
        else:
            if len(run) >= 3:
                toc.append((segs[run[0]]["line"], segs[run[-1]]["line"], len(run)))
            run = [k]
    if len(run) >= 3:
        toc.append((segs[run[0]]["line"], segs[run[-1]]["line"], len(run)))
    # 重号：卷内比。很多书每卷从第1章重排，跨卷同号是正常的；
    # 同卷同号但标题不同的（如卷末「第1章 番外」重新起号）也不算重号
    groups = {}
    for s in segs:
        if s["kind"] == "chapter" and s["num"] is not None:
            groups.setdefault((s["vol"], s["num"]), []).append(s)
    dups = {}
    for k, lst in groups.items():
        if len(lst) < 2:
            continue
        by_title = {}
        for s in lst:
            by_title.setdefault(v6_title_key(s["raw"]), []).append(s)
        sub = [s for g in by_title.values() if len(g) > 1 for s in g]
        if sub:
            dups[k] = sub
    # 卷内连续性
    by_vol = {}
    for s in segs:
        if s["kind"] == "chapter" and s["num"] is not None:
            by_vol.setdefault(s["vol"], []).append(s)
    jumps, gaps = [], []
    for v, lst in sorted(by_vol.items()):
        for a, b in zip(lst, lst[1:]):
            if b["num"] > a["num"] + 1:      # 只报向前跳号；向后重起号（番外另起）不算
                jumps.append({"vol": v, "from": a["num"], "to": b["num"], "line": b["line"]})
        have = {x["num"] for x in lst}
        miss = [n for n in range(1, max(have) + 1) if n not in have]
        if miss:
            gaps.append({"vol": v, "miss": miss})
    longs = [s for s in segs if s["chars"] > long_chars]
    return segs, vols, {"dups": dups, "jumps": jumps, "gaps": gaps, "toc": toc,
                        "longs": longs, "indented": [s for s in segs if s["indented"]]}


def v6_dup_label(key):
    v, n = key
    return (f"卷{v}-章{n}" if v else f"章{n}")


def v6_filter_dups(segs, dups, policy):
    keep, drop = [], []
    for s in segs:
        key = (s["vol"], s["num"]) if (s["kind"] == "chapter" and s["num"] is not None) else None
        vs = dups.get(key) if key else None
        if not vs or policy == "都保留":
            keep.append(s)
            continue
        cho = (next((x for x in vs if "修订" in x["raw"]), vs[-1])
               if policy == "修订版" else vs[0])
        (keep if s is cho else drop).append(s)
    return keep, drop


def v6_seg_body(lines, s):
    return "\n".join(lines[s["line"] - 1:s["end"]]).rstrip() + "\n"


# ==================== 流水线（GUI / 命令行共用） ====================
def run_pipeline(src, out_root, cfg, log=None, progress=None, cur=None, gate=None):
    """扫全书 → 判歧义 → 按 cfg['mode'] 落盘。返回 dict（GUI 直接拿去显示）。"""
    log = log or (lambda m: None)
    progress = progress or (lambda d, t: None)
    cur = cur or (lambda s: None)
    gate = gate or (lambda: True)
    t0 = time.time()
    mode = (cfg.get("mode") or "chapter").strip()
    content = read_text_any(src)
    base_name = os.path.splitext(os.path.basename(src))[0]
    task = os.path.join(out_root, f"{time.strftime('%Y%m%d_%H%M%S')}_{base_name}")
    k = 2
    while os.path.exists(task):      # 同一秒跑两次也别混进同一个目录
        task = f"{os.path.join(out_root, time.strftime('%Y%m%d_%H%M%S') + '_' + base_name)}_{k}"
        k += 1
    os.makedirs(task, exist_ok=True)
    log("模式：" + MODE_NAMES.get(mode, mode))
    log("结果目录：" + task)

    # ① 扫描（章节候选 + 卷候选一起进 heads，kind 决定用途）
    cur("扫描全书…")
    lines, heads, amb = v5_scan(content)
    seen_v = ({h["line"] for h in heads if h.get("kind") == "volume"} |
              {a["line"] for a in amb if a.get("kind") == "volume"})
    for v in v6_volume_candidates(lines):
        if v["line"] in seen_v:      # v5_scan 已经抓到「第N卷」样式，别重复记
            continue
        if v["indented"]:
            amb.append(dict(v, why="标题带缩进"))
        else:
            heads.append(v)
    promoted, left = v5_promote_by_structure(heads, amb)
    heads = heads + promoted
    log(f"扫描完成：{len(lines):,} 行 / {len(content):,} 字符｜确定标题 {len(heads)} 条"
        f"（其中卷标题 {sum(1 for h in heads if h.get('kind') == 'volume')} 条）｜"
        f"结构补全 {len(promoted)} 条｜待判歧义 {len(left)} 条")

    # ② 模型判歧义（可暂停/停止）
    judge_n, judged_head, judge_err = 0, 0, None
    if left and cfg.get("enable_ai"):
        try:
            client = V5JudgeClient(cfg)
            batch = max(1, int(cfg.get("v5_batch", 20)))
            for i in range(0, len(left), batch):
                if not gate():
                    return {"stopped": True, "msg": "已停止（未落盘）", "task": task}
                part = left[i:i + batch]
                cases = []
                for k, k2 in enumerate(part, 1):
                    ln = k2["line"]
                    cases.append({"idx": k, "prev": lines[ln - 2] if ln >= 2 else "",
                                  "line": lines[ln - 1], "nxt": lines[ln] if ln < len(lines) else ""})
                res, err = client.judge(cases)
                if err and not res:
                    judge_err = err
                    break
                for k, k2 in enumerate(part, 1):
                    is_h, kind = res.get(k, (None, None))
                    k2["model"] = (is_h, kind)
                    if is_h:
                        heads.append(dict(k2, kind=k2["kind"] or
                                          ("chapter" if kind == "chapter" else "extra")))
                        judged_head += 1
                    judge_n += 1
                done = i + len(part)
                progress(done, max(len(left), 1))
                cur(f"判歧义 {done}/{len(left)}")
                log(f"  模型判歧义 {done}/{len(left)}")
        except Exception as e:
            judge_err = f"{type(e).__name__}: {e}"
    elif left:
        judge_err = "未启用模型，歧义候选按正文处理"

    if not gate():
        return {"stopped": True, "msg": "已停止（未落盘）", "task": task}

    ctx = {"lines": lines, "heads": heads, "promoted": promoted, "left": left,
           "judge_n": judge_n, "judged_head": judged_head, "judge_err": judge_err,
           "content": content, "src": src, "base_name": base_name, "task": task,
           "cfg": cfg, "t0": t0, "log": log, "progress": progress, "cur": cur, "gate": gate}
    if mode == "volume":
        return _mode_volume(ctx)
    if mode == "chunk":
        return _mode_chunk(ctx)
    return _mode_chapter(ctx)


# ==================== 模式一：分章（原有行为 + 卷内判重） ====================
def _mode_chapter(ctx):
    c, lines, task = ctx["cfg"], ctx["lines"], ctx["task"]
    log, progress, cur, gate = ctx["log"], ctx["progress"], ctx["cur"], ctx["gate"]
    src, base_name = ctx["src"], ctx["base_name"]
    policy = c.get("v5_dup_policy", "修订版")
    segs, vols, insp = v6_finalize(lines, ctx["heads"], policy,
                                   c.get("v5_long_block_chars", 40000), c.get("v5_toc_gap", 2))
    keep, drop = v6_filter_dups(segs, insp["dups"], policy)

    files = []
    for idx, s in enumerate(keep, 1):
        if not gate():
            return {"stopped": True, "msg": f"已停止（已写出 {idx-1} 章）", "task": task}
        fn = f"{idx:03d}_{sanitize_filename(s['raw'])[:40]}.txt"
        open(os.path.join(task, fn), "w", encoding="utf-8").write(v6_seg_body(lines, s))
        files.append({"file": fn, "num": s["num"], "vol": s["vol"], "vol_title": s["vol_title"],
                      "line": s["line"], "chars": s["chars"], "title": s["raw"][:60],
                      "promoted_by": s.get("promoted_by", "")})
        progress(idx, max(len(keep), 1))
        cur(fn[:30])

    if drop:
        old = os.path.join(task, "_原始稿_未采用")
        os.makedirs(old, exist_ok=True)
        for s in drop:
            fn = f"原始稿_L{s['line']}_{sanitize_filename(s['raw'])[:30]}.txt"
            open(os.path.join(old, fn), "w", encoding="utf-8").write(v6_seg_body(lines, s))

    nums = [f["num"] for f in files if f["num"]]
    stats = {"mode": "chapter", "chapters": len(files), "volumes": len(vols),
             "lines": len(lines), "chars": len(ctx["content"]),
             "candidates": len(ctx["heads"]) + len(ctx["left"]),
             "promoted": len(ctx["promoted"]), "ambiguous": len(ctx["left"]),
             "judged": ctx["judge_n"], "judged_heading": ctx["judged_head"],
             "dups": [v6_dup_label(k) for k in sorted(insp["dups"])],
             "gaps": insp["gaps"], "jumps": len(insp["jumps"]), "toc": insp["toc"],
             "longs": [[(s["num"] if s["num"] else s["raw"][:12]), s["chars"]]
                       for s in insp["longs"][:8]],
             "indented": len(insp["indented"]), "dropped": len(drop),
             "dup_policy": policy, "judge_err": ctx["judge_err"],
             "seconds": round(time.time() - ctx["t0"], 1),
             "num_min": min(nums) if nums else 0, "num_max": max(nums) if nums else 0}
    json.dump({"stats": stats, "chapters": files,
               "repaired": [{"line": x["line"], "raw": x["raw"],
                             "by": x.get("promoted_by", "模型")} for x in ctx["promoted"]]},
              open(os.path.join(task, "chapters.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)

    rep = [f"# {base_name} 分章体检报告", "",
           f"- 源文件：{os.path.basename(src)}（{len(lines):,} 行 / {len(ctx['content']):,} 字符）",
           f"- 模式：分章（一章一文件）",
           f"- 标题候选 {len(ctx['heads']) + len(ctx['left'])} 条：结构补全 {len(ctx['promoted'])} 条、"
           f"模型判定 {ctx['judge_n']} 条（其中判为标题 {ctx['judged_head']} 条）",
           f"- 输出章数 **{len(files)}**，章号 {stats['num_min']} – {stats['num_max']}"
           f"（共识别 {len(vols)} 卷，重号按卷内比较）",
           f"- 重号：{stats['dups'] or '无'}　缺号（卷内）：{stats['gaps'] or '无'}　"
           f"跳号 {stats['jumps']} 处",
           f"- 重号处理：{policy}（未采用的在 _原始稿_未采用/，没删）",
           f"- 目录页疑似：{stats['toc'] or '未发现'}",
           f"- 带缩进的标题：{stats['indented']} 条",
           f"- 超长块：{stats['longs'] or '无'}",
           f"- 模型状态：{ctx['judge_err'] or '正常'}",
           f"- 耗时：{stats['seconds']} 秒", "",
           "## 补全 / 判定的标题", ""]
    for x in ctx["promoted"]:
        rep.append(f"- L{x['line']}（{x.get('promoted_by')}）`{x['raw'][:50]}`")
    for x in ctx["left"]:
        m = x.get("model")
        if m and m[0]:
            rep.append(f"- L{x['line']}（模型判标题）`{x['raw'][:50]}`")
        elif m:
            rep.append(f"- L{x['line']}（模型判正文，已排除）`{x['raw'][:50]}`")
        else:
            rep.append(f"- L{x['line']}（未判定，按正文）`{x['raw'][:50]}`")
    rep += ["", "## 章节索引", "", "| # | 卷 | 章号 | 源行 | 字数 | 标题 |",
            "|---|---|---|---|---|---|"]
    for i, f_ in enumerate(files, 1):
        rep.append(f"| {i} | {f_['vol'] or '-'} | {f_['num'] or '-'} | {f_['line']} | "
                   f"{f_['chars']:,} | {f_['title'][:30]} |")
    open(os.path.join(task, "分章体检报告.md"), "w", encoding="utf-8").write("\n".join(rep))

    progress(100, 100)
    msg = (f"✅ 分章完成：{len(files)} 章（章号 {stats['num_min']}–{stats['num_max']}）\n"
           f"识别到 {len(vols)} 卷；结构补全 {len(ctx['promoted'])} 条、模型判定 {ctx['judge_n']} 条\n"
           f"重号 {stats['dups'] or '无'}　缺号 {stats['gaps'] or '无'}\n\n"
           f"结果目录：\n{task}\n\n（含 分章体检报告.md 与 chapters.json）")
    return {"ok": True, "task": task, "mode": "chapter", "files": len(files),
            "stat": (f"{len(files)} 章｜{len(vols)} 卷｜补全 {len(ctx['promoted'])}｜"
                     f"模型判 {ctx['judge_n']}｜重号 {len(stats['dups'])}｜{stats['seconds']}s"),
            "msg": msg, "stats": stats}


# ==================== 模式二：分卷（按第N卷/部/篇/集 切） ====================
def _mode_volume(ctx):
    c, lines, task = ctx["cfg"], ctx["lines"], ctx["task"]
    log, progress, cur, gate = ctx["log"], ctx["progress"], ctx["cur"], ctx["gate"]
    ranges, vols = v6_volume_ranges(lines, ctx["heads"])
    if len(vols) < 2:
        try:
            if not os.listdir(task):
                os.rmdir(task)     # 别留空目录
        except Exception:
            pass
        raise RuntimeError(
            f"只识别到 {len(vols)} 个卷标题（第N卷/部/篇/集）。这本书用「分卷」切不出多卷，"
            "请改用「分章」或「分块」模式；若确实分了卷，请确认卷标题单独成行"
            "（如「第一卷 风起云涌」），且卷号递增。")
    files = []
    for r in ranges:
        if not gate():
            return {"stopped": True, "msg": f"已停止（已写出 {len(files)} 卷）", "task": task}
        fn = f"{r['idx']:03d}_{sanitize_filename(str(r['title']))[:40]}.txt"
        body = "\n".join(lines[r["start"] - 1:r["end"]]).rstrip() + "\n"
        open(os.path.join(task, fn), "w", encoding="utf-8").write(body)
        nums = [h["num"] for h in ctx["heads"]
                if h.get("kind") == "chapter" and r["start"] <= h["line"] <= r["end"]
                and h.get("num") is not None]
        rec = {"file": fn, "idx": r["idx"], "title": r["title"], "start": r["start"],
               "end": r["end"], "chars": r["chars"], "tokens": count_tokens(body),
               "chapters": len(nums),
               "ch_from": min(nums) if nums else None, "ch_to": max(nums) if nums else None}
        files.append(rec)
        log(f"  第{r['idx']}卷 → {fn}（{rec['chapters']} 章 / {r['chars']:,} 字 / "
            f"≈{rec['tokens']:,} token）")
        progress(len(files), max(len(ranges), 1))
        cur(fn[:30])

    total_tok = sum(f["tokens"] for f in files)
    method = tokens_method()
    json.dump({"mode": "volume", "token_method": method, "volumes": files},
              open(os.path.join(task, "volumes.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)
    rep = [f"# {ctx['base_name']} 分卷报告", "",
           f"- 源文件：{os.path.basename(ctx['src'])}"
           f"（{len(lines):,} 行 / {len(ctx['content']):,} 字符）",
           f"- 模式：分卷（一卷一文件，卷内章节保持原样不切）",
           f"- 卷数 **{len(vols)}**（另有开篇 {1 if ranges and ranges[0]['idx'] == 0 else 0} 段），"
           f"总 ≈{total_tok:,} token（{method}）",
           f"- 模型状态：{ctx['judge_err'] or '正常'}",
           f"- 耗时：{round(time.time() - ctx['t0'], 1)} 秒", "",
           "| 文件 | 卷 | 源行 | 章数 | 章号范围 | 字符 | ≈token |",
           "|---|---|---|---|---|---|---|"]
    for f_ in files:
        rng = (f"{f_['ch_from']}-{f_['ch_to']}" if f_["ch_from"] is not None else "-")
        rep.append(f"| {f_['file']} | {f_['title'][:24]} | {f_['start']}-{f_['end']} | "
                   f"{f_['chapters']} | {rng} | {f_['chars']:,} | {f_['tokens']:,} |")
    rep += ["", "## 识别到的卷界限", ""]
    for v in vols:
        rep.append(f"- L{v['line']} `{v['raw'][:50]}`")
    open(os.path.join(task, "分卷报告.md"), "w", encoding="utf-8").write("\n".join(rep))

    progress(100, 100)
    msg = (f"✅ 分卷完成：{len(files)} 个文件（{len(vols)} 卷），"
           f"总计 ≈{total_tok:,} token（{method}）\n"
           f"结构补全 {len(ctx['promoted'])} 条、模型判定 {ctx['judge_n']} 条\n\n"
           f"结果目录：\n{task}\n\n（含 分卷报告.md 与 volumes.json）")
    return {"ok": True, "task": task, "mode": "volume", "files": len(files),
            "stat": (f"{len(vols)} 卷｜≈{total_tok:,} token｜{ctx['judge_n']} 条模型判定"),
            "msg": msg, "stats": {"volumes": files, "tokens": total_tok}}


# ==================== 模式三：分块（分章后按累计 token 合并，不跨卷） ====================
def _chunk_name(ci, items):
    v = items[0]["vol"]
    volpart = f"第{v}卷" if v else "卷前"
    a, b = items[0]["num"], items[-1]["num"]
    if a is not None and b is not None:
        rng = f"章{a:02d}-{b:02d}" if a != b else f"章{a:02d}"
    else:
        rng = f"序{items[0]['idx']:03d}-{items[-1]['idx']:03d}"
    return f"chunk{ci:03d}_{volpart}_{rng}"


def v6_group_chunks(items, limit):
    """贪心合并：同一卷内累计 token 最接近且不超 limit；跨卷一定断开。"""
    chunks, cur, acc = [], [], 0
    for it in items:
        if cur and it["vol"] != cur[-1]["vol"]:
            chunks.append((cur, acc))
            cur, acc = [], 0
        if cur and acc + it["tokens"] > limit:
            chunks.append((cur, acc))
            cur, acc = [], 0
        cur.append(it)
        acc += it["tokens"]
    if cur:
        chunks.append((cur, acc))
    return chunks


def _mode_chunk(ctx):
    c, lines, task = ctx["cfg"], ctx["lines"], ctx["task"]
    log, progress, cur, gate = ctx["log"], ctx["progress"], ctx["cur"], ctx["gate"]
    policy = c.get("v5_dup_policy", "修订版")
    limit = max(500, int(c.get("v6_chunk_tokens", 30000) or 30000))
    segs, vols, insp = v6_finalize(lines, ctx["heads"], policy,
                                   c.get("v5_long_block_chars", 40000), c.get("v5_toc_gap", 2))
    keep, drop = v6_filter_dups(segs, insp["dups"], policy)

    items = []
    for i, s in enumerate(keep, 1):
        if not gate():
            return {"stopped": True, "msg": "已停止（未落盘）", "task": task}
        body = v6_seg_body(lines, s)
        items.append({"idx": i, "line": s["line"], "end": s["end"], "raw": s["raw"],
                      "num": s["num"], "kind": s["kind"], "vol": s["vol"],
                      "vol_title": s["vol_title"], "chars": len(body),
                      "tokens": count_tokens(body), "body": body})
        if i % 50 == 0:
            progress(i, max(len(keep), 1))
            cur(f"算 token {i}/{len(keep)}")
            log(f"  统计 token {i}/{len(keep)}")

    groups = v6_group_chunks(items, limit)
    log(f"合并完成：{len(items)} 个章节 → {len(groups)} 个块（每块上限 {limit:,} token，"
        f"不跨卷）")

    if c.get("v6_keep_chapter_files", True):
        chap_dir = os.path.join(task, "_单章")
        os.makedirs(chap_dir, exist_ok=True)
        for it in items:
            fn = f"{it['idx']:04d}_{sanitize_filename(it['raw'])[:40]}.txt"
            open(os.path.join(chap_dir, fn), "w", encoding="utf-8").write(it["body"])

    files = []
    for ci, (grp, acc) in enumerate(groups, 1):
        if not gate():
            return {"stopped": True, "msg": f"已停止（已写出 {len(files)} 块）", "task": task}
        name = _chunk_name(ci, grp)
        fn = name + ".txt"
        open(os.path.join(task, fn), "w", encoding="utf-8").write(
            "".join(x["body"] for x in grp))
        nums = [x["num"] for x in grp if x["num"] is not None]
        files.append({"chunk": name, "file": fn, "vol": grp[0]["vol"],
                      "vol_title": grp[0]["vol_title"],
                      "chapters": len(grp),
                      "ch_from": min(nums) if nums else None,
                      "ch_to": max(nums) if nums else None,
                      "first_title": grp[0]["raw"][:60], "last_title": grp[-1]["raw"][:60],
                      "chars": sum(x["chars"] for x in grp), "tokens": acc,
                      "line_from": grp[0]["line"], "line_to": grp[-1]["end"],
                      "oversize": (len(grp) == 1 and acc > limit),
                      "single_oversize_chars": (grp[0]["chars"] if len(grp) == 1 and acc > limit else 0)})
        progress(len(files), max(len(groups), 1))
        cur(fn[:30])
        log(f"  {fn}（{len(grp)} 章 / ≈{acc:,} token）")

    method = tokens_method()
    total_tok = sum(f["tokens"] for f in files)
    oversize = [f for f in files if f["oversize"]]
    json.dump({"mode": "chunk", "token_method": method, "limit": limit,
               "token_total": total_tok, "chunk_count": len(files),
               "chapters": len(items), "volumes": len(vols),
               "chunks": files,
               "chapter_index": [{k: it[k] for k in ("idx", "vol", "num", "raw", "line", "chars", "tokens")}
                                 for it in items],
               "dups": [v6_dup_label(k) for k in sorted(insp["dups"])],
               "gaps": insp["gaps"], "judge_err": ctx["judge_err"]},
              open(os.path.join(task, "chunks.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)

    rep = [f"# {ctx['base_name']} 分块报告", "",
           f"- 源文件：{os.path.basename(ctx['src'])}"
           f"（{len(lines):,} 行 / {len(ctx['content']):,} 字符）",
           f"- 模式：分块（先分章 → 卷内按累计 token 贪心合并）",
           f"- 目标块大小：**{limit:,} token**（估算方式：{method}）",
           f"- 结果：{len(items)} 个章节 → **{len(files)} 个块**，总 ≈{total_tok:,} token，"
           f"识别 {len(vols)} 卷",
           f"- 规则：同一块不跨卷；卷尾加不下下一章时，剩余章节单独成块，下一卷从新块开始",
           f"- 重号处理：{policy}　重号（卷内）：{[v6_dup_label(k) for k in sorted(insp['dups'])] or '无'}",
           f"- 超限单章：{len(oversize)} 个（单章自身就超过 {limit:,} token，只能独占一块）",
           f"- 模型状态：{ctx['judge_err'] or '正常'}",
           f"- 耗时：{round(time.time() - ctx['t0'], 1)} 秒", "",
           "| 块文件 | 卷 | 卷内章号 | 章数 | 字符 | ≈token | 占上限 | 备注 |",
           "|---|---|---|---|---|---|---|---|"]
    for f_ in files:
        rng = (f"{f_['ch_from']}-{f_['ch_to']}" if f_["ch_from"] is not None else "-")
        note = "超限单章" if f_["oversize"] else ""
        rep.append(f"| {f_['file']} | {f_['vol'] or '卷前'} | {rng} | {f_['chapters']} | "
                   f"{f_['chars']:,} | {f_['tokens']:,} | {f_['tokens'] * 100.0 / limit:.0f}% | {note} |")
    open(os.path.join(task, "分块报告.md"), "w", encoding="utf-8").write("\n".join(rep))

    progress(100, 100)
    msg = (f"✅ 分块完成：{len(items)} 章 → {len(files)} 个块"
           f"（每块上限 {limit:,} token，{method}）\n"
           f"识别 {len(vols)} 卷，不跨卷合并；超限单章 {len(oversize)} 个\n"
           f"总 ≈{total_tok:,} token\n\n"
           f"结果目录：\n{task}\n\n（块文件在根目录，单章在 _单章/，含 分块报告.md 与 chunks.json）")
    if len(items) <= 1:
        msg = ("⚠ 只识别到 " + str(len(items)) + " 个标题段，分块没意义：\n"
               "请先确认章节标题（第X章）单独成行，或用「分章」模式看体检报告。\n\n" + msg)
    if oversize and len(oversize) == len(files):
        msg = ("⚠ 每一章都超过上限，块=章：目标块大小设大一点，或先降低单章长度。\n\n" + msg)
    return {"ok": True, "task": task, "mode": "chunk", "files": len(files),
            "stat": (f"{len(files)} 块｜{len(items)} 章｜上限 {limit:,}｜≈{total_tok:,} token｜"
                     f"{round(time.time() - ctx['t0'], 1)}s"),
            "msg": msg, "stats": {"chunks": files, "tokens": total_tok}}


# ==================== GUI ====================
class ChapterSplitterApp:
    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.cfg = load_cfg()
        self.src = tk.StringVar(value="")
        self.out = tk.StringVar(value=self.cfg.get("last_out", ""))
        self.enable_ai = tk.BooleanVar(value=bool(self.cfg.get("enable_ai", True)))
        self.api_url = tk.StringVar(value=self.cfg.get("api_url", ""))
        self.api_key = tk.StringVar(value=self.cfg.get("api_key", ""))
        self.model = tk.StringVar(value=self.cfg.get("model", ""))
        self.timeout = tk.StringVar(value=str(self.cfg.get("timeout", 600)))
        self.long_chars = tk.StringVar(value=str(self.cfg.get("v5_long_block_chars", 40000)))
        self.batch = tk.StringVar(value=str(self.cfg.get("v5_batch", 20)))
        self.dup = tk.StringVar(value=self.cfg.get("v5_dup_policy", "修订版"))
        self.toc_gap = tk.StringVar(value=str(self.cfg.get("v5_toc_gap", 2)))
        self.mode = tk.StringVar(value=self.cfg.get("mode", "chapter"))
        self.chunk_tokens = tk.StringVar(value=str(self.cfg.get("v6_chunk_tokens", 30000)))
        self.tok_method_text = tk.StringVar(value="")
        self.progress = tk.DoubleVar(value=0)
        self.progress_text = tk.StringVar(value="0 / 0")
        self.state_text = tk.StringVar(value="就绪")
        self.cur_text = tk.StringVar(value="—")
        self.stat_text = tk.StringVar(value="未开始")
        self.running = False
        self.paused = False
        self.stop_event = threading.Event()
        self.run_event = threading.Event()
        self.worker = None
        self.last_dir = ""
        self._build()
        self.log("程序就绪。选一个小说 txt，配好 API（也可以关掉模型只用规则），点「开始分章」。")

    def _build(self):
        r = self.root
        r.geometry("920x775")
        r.grid_columnconfigure(0, weight=1)
        r.grid_rowconfigure(3, weight=1)

        f1 = tk.LabelFrame(r, text="① 文件与输出", padx=8, pady=6)
        f1.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 4))
        f1.grid_columnconfigure(1, weight=1)
        tk.Label(f1, text="小说 txt:").grid(row=0, column=0, sticky="e")
        tk.Entry(f1, textvariable=self.src).grid(row=0, column=1, sticky="ew", padx=4)
        tk.Button(f1, text="选择", width=8, command=self.pick_src).grid(row=0, column=2, padx=2)
        tk.Label(f1, text="输出目录:").grid(row=1, column=0, sticky="e", pady=4)
        tk.Entry(f1, textvariable=self.out).grid(row=1, column=1, sticky="ew", padx=4)
        tk.Button(f1, text="选择", width=8, command=self.pick_out).grid(row=1, column=2, padx=2)
        tk.Button(f1, text="打开", width=8, command=self.open_out).grid(row=1, column=3, padx=2)
        tk.Label(f1, foreground="gray", justify="left", wraplength=820, text=(
            "输出放在「输出目录 / 任务时间_文件名 /」里　·　分章：逐章 txt + 分章体检报告.md + chapters.json"
            "　·　分卷：一卷一 txt + 分卷报告.md + volumes.json"
            "　·　分块：chunk001_第1卷_章01-07.txt … + _单章/ + 分块报告.md + chunks.json"
        )).grid(row=2, column=0, columnspan=4, sticky="w", pady=(2, 0))

        f2 = tk.LabelFrame(r, text="② 模型 API（可关，关掉＝纯规则分章）", padx=8, pady=6)
        f2.grid(row=1, column=0, sticky="ew", padx=10, pady=4)
        f2.grid_columnconfigure(1, weight=1)
        tk.Checkbutton(f2, text="启用模型判歧义", variable=self.enable_ai).grid(
            row=0, column=0, columnspan=2, sticky="w")
        for i, (lab, var, show) in enumerate((("地址", self.api_url, ""), ("密钥", self.api_key, "*"),
                                              ("模型", self.model, ""), ("超时(秒)", self.timeout, "")), start=1):
            tk.Label(f2, text=lab + ":").grid(row=i, column=0, sticky="e")
            tk.Entry(f2, textvariable=var, show=show).grid(row=i, column=1, sticky="ew", padx=4, pady=2)
        bf = tk.Frame(f2)
        bf.grid(row=1, column=2, rowspan=4, padx=6)
        self.btn_test = tk.Button(bf, text="测试连接\n取模型名", width=12, command=self.test_api)
        self.btn_test.pack(pady=2)
        tk.Button(bf, text="保存配置", width=12, command=self.save_all).pack(pady=2)

        f3 = tk.LabelFrame(r, text="③ 模式与体检参数", padx=8, pady=6)
        f3.grid(row=2, column=0, sticky="ew", padx=10, pady=4)
        for i in range(6):
            f3.grid_columnconfigure(i, weight=1)
        mrow = tk.Frame(f3)
        mrow.grid(row=0, column=0, columnspan=6, sticky="w")
        tk.Label(mrow, text="模式：").pack(side="left")
        for val, lab in (("chapter", "分章"), ("volume", "分卷"), ("chunk", "分块（按token合并）")):
            tk.Radiobutton(mrow, text=lab, variable=self.mode, value=val,
                           command=self._mode_changed).pack(side="left", padx=(0, 8))
        tk.Label(mrow, text="　目标块大小(token)：").pack(side="left")
        self.ent_chunk = tk.Entry(mrow, textvariable=self.chunk_tokens, width=9)
        self.ent_chunk.pack(side="left")
        tk.Label(mrow, textvariable=self.tok_method_text, fg="gray").pack(side="left", padx=8)
        tk.Label(f3, text="超长块阈值(字符)").grid(row=1, column=0, sticky="e", pady=(6, 0))
        tk.Entry(f3, textvariable=self.long_chars, width=8).grid(row=1, column=1, sticky="w", pady=(6, 0))
        tk.Label(f3, text="每批候选数").grid(row=1, column=2, sticky="e", pady=(6, 0))
        tk.Entry(f3, textvariable=self.batch, width=8).grid(row=1, column=3, sticky="w", pady=(6, 0))
        tk.Label(f3, text="目录页间距(行)").grid(row=1, column=4, sticky="e", pady=(6, 0))
        tk.Entry(f3, textvariable=self.toc_gap, width=8).grid(row=1, column=5, sticky="w", pady=(6, 0))
        tk.Label(f3, text="重号处理").grid(row=2, column=0, sticky="e", pady=(4, 0))
        tk.OptionMenu(f3, self.dup, "修订版", "原始版", "都保留").grid(row=2, column=1, sticky="w", pady=(4, 0))
        self._mode_changed()


        f4 = tk.LabelFrame(r, text="④ 运行", padx=8, pady=6)
        f4.grid(row=3, column=0, sticky="nsew", padx=10, pady=(4, 10))
        f4.grid_columnconfigure(0, weight=1)
        f4.grid_rowconfigure(3, weight=1)

        bar = tk.Frame(f4)
        bar.grid(row=0, column=0, sticky="ew")
        self.btn_start = tk.Button(bar, text="▶ 开始分章", width=12, command=self.start)
        self.btn_start.pack(side="left", padx=2)
        self.btn_pause = tk.Button(bar, text="⏸ 暂停", width=10, command=self.toggle_pause, state="disabled")
        self.btn_pause.pack(side="left", padx=2)
        self.btn_stop = tk.Button(bar, text="⏹ 停止", width=10, command=self.stop, state="disabled")
        self.btn_stop.pack(side="left", padx=2)
        tk.Label(bar, textvariable=self.state_text, fg="#2c3e50").pack(side="left", padx=12)
        tk.Label(bar, textvariable=self.stat_text, fg="gray").pack(side="left")

        self.pbar = ttk.Progressbar(f4, variable=self.progress, maximum=100)
        self.pbar.grid(row=1, column=0, sticky="ew", pady=(8, 2))
        info = tk.Frame(f4)
        info.grid(row=2, column=0, sticky="ew")
        tk.Label(info, textvariable=self.progress_text).pack(side="left")
        tk.Label(info, text="  当前：").pack(side="left")
        tk.Label(info, textvariable=self.cur_text, fg="#c0392b").pack(side="left")

        self.log_box = scrolledtext.ScrolledText(f4, height=12, font=("Consolas", 9))
        self.log_box.grid(row=3, column=0, sticky="nsew", pady=(6, 0))

    def _mode_changed(self):
        chunk = (self.mode.get() == "chunk")
        try:
            self.ent_chunk.config(state="normal" if chunk else "disabled")
        except Exception:
            pass
        try:
            self.tok_method_text.set(("（" + tokens_method() + "）") if chunk else "")
        except Exception:
            self.tok_method_text.set("")

    # ---------------- 小工具 ----------------
    def log(self, msg):
        try:
            self.log_box.insert("end", f"[{time.strftime('%H:%M:%S')}] {msg}\n")
            self.log_box.see("end")
        except Exception:
            pass

    def ui(self, fn, *a):
        self.root.after(0, lambda: fn(*a))

    def pick_src(self):
        p = filedialog.askopenfilename(title="选择小说 txt", filetypes=[("文本", "*.txt"), ("全部", "*.*")])
        if p:
            self.src.set(p)
            if not self.out.get().strip():
                self.out.set(os.path.dirname(p))

    def pick_out(self):
        p = filedialog.askdirectory(title="选择输出目录")
        if p:
            self.out.set(p)

    def open_out(self):
        p = self.last_dir or self.out.get().strip()
        if p and os.path.isdir(p):
            os.startfile(p)
        else:
            messagebox.showinfo("提示", "还没有结果目录（开始分章后自动创建）")

    def collect(self):
        try:
            c = {
                "enable_ai": bool(self.enable_ai.get()),
                "api_url": normalize_api_url(self.api_url.get()),
                "api_key": self.api_key.get().strip(),
                "model": self.model.get().strip(),
                "timeout": int(float(self.timeout.get() or 600)),
                "max_retries": int(float(self.cfg.get("max_retries", 3))),
                "v5_long_block_chars": int(float(self.long_chars.get() or 40000)),
                "v5_batch": int(float(self.batch.get() or 20)),
                "v5_dup_policy": self.dup.get(),
                "v5_toc_gap": int(float(self.toc_gap.get() or 2)),
                "mode": self.mode.get(),
                "v6_chunk_tokens": int(float(self.chunk_tokens.get() or 30000)),
                "v6_keep_chapter_files": bool(self.cfg.get("v6_keep_chapter_files", True)),
                "last_out": self.out.get().strip(),
            }
        except ValueError as e:
            raise ValueError(f"参数必须是数字：{e}")
        if c["enable_ai"]:
            if not c["api_url"].startswith("http"):
                raise ValueError("启用模型时，API 地址要以 http:// 或 https:// 开头")
            if not c["model"]:
                raise ValueError("启用模型时必须填模型名（可点「测试连接/取模型名」）")
        if c["v5_batch"] < 1:
            raise ValueError("每批候选数必须 >= 1")
        if c["mode"] == "chunk" and c["v6_chunk_tokens"] < 500:
            raise ValueError("分块模式的目标块大小必须 >= 500 token")
        return c

    def save_all(self):
        try:
            c = self.collect()
        except ValueError as e:
            messagebox.showerror("参数错误", str(e))
            return
        save_cfg(c)
        self.log("配置已保存到 " + CFG_FILE)

    def test_api(self):
        if requests is None:
            messagebox.showerror("缺少依赖", "没有安装 requests：在 .venv 里 pip install requests")
            return
        try:
            c = self.collect()
        except ValueError as e:
            messagebox.showerror("参数错误", str(e))
            return
        self.btn_test.config(state="disabled")
        self.log("测试连接：" + c["api_url"])

        def work():
            try:
                base = c["api_url"].rsplit("/chat/completions", 1)[0]
                h = {"Content-Type": "application/json"}
                if c["api_key"]:
                    h["Authorization"] = "Bearer " + c["api_key"]
                d = requests.get(base + "/models", headers=h, timeout=15).json()
                items = d.get("data") or d.get("models") or []
                names = [pretty_model_name(m.get("id") or m.get("name")) for m in items if isinstance(m, dict)]
                self.ui(self._test_done, [n for n in names if n], None)
            except Exception as e:
                self.ui(self._test_done, [], f"{type(e).__name__}: {e}")
        threading.Thread(target=work, daemon=True).start()

    def _test_done(self, names, err):
        self.btn_test.config(state="normal")
        if err:
            self.log("连接失败：" + err)
            messagebox.showerror("连接失败", err)
            return
        cur = self.model.get().strip()
        if names and cur not in names:
            self.model.set(names[0])
            self.log(f"连接成功，已自动填入模型名：{names[0]}")
        else:
            self.log("连接成功，端点模型：" + ("、".join(names[:5]) if names else "（空）"))

    # ---------------- 运行控制 ----------------
    def start(self):
        if self.running:
            return
        try:
            c = self.collect()
        except ValueError as e:
            messagebox.showerror("参数错误", str(e))
            return
        if c["enable_ai"] and requests is None:
            messagebox.showerror("缺少依赖", "没有安装 requests：在 .venv 里 pip install requests")
            return
        src = self.src.get().strip()
        if not src or not os.path.exists(src):
            messagebox.showerror("缺少文件", "请先选择小说 txt")
            return
        if not self.out.get().strip():
            messagebox.showerror("缺少输出", "请先选择输出目录")
            return
        save_cfg(c)
        self.stop_event.clear()
        self.run_event.set()
        self.running = True
        self.paused = False
        self.btn_start.config(state="disabled")
        self.btn_pause.config(state="normal", text="⏸ 暂停")
        self.btn_stop.config(state="normal")
        self.state_text.set("运行中")
        self.log("=" * 44)
        self.worker = threading.Thread(target=self._run, args=(src, c), daemon=True)
        self.worker.start()

    def toggle_pause(self):
        if not self.running:
            return
        if self.paused:
            self.run_event.set()
            self.paused = False
            self.btn_pause.config(text="⏸ 暂停")
            self.state_text.set("运行中")
            self.log("▶ 继续")
        else:
            self.run_event.clear()
            self.paused = True
            self.btn_pause.config(text="▶ 继续")
            self.state_text.set("已暂停")
            self.log("⏸ 暂停（当前请求返回后停住）")

    def stop(self):
        if not self.running:
            return
        self.stop_event.set()
        self.run_event.set()
        self.state_text.set("正在停止…")
        self.log("⏹ 收到停止请求")

    def _gate(self):
        while not self.run_event.is_set():
            if self.stop_event.is_set():
                return False
            time.sleep(0.15)
        return not self.stop_event.is_set()

    def _finish(self, ok, msg):
        self.running = False
        self.paused = False
        self.btn_start.config(state="normal")
        self.btn_pause.config(state="disabled", text="⏸ 暂停")
        self.btn_stop.config(state="disabled")
        self.state_text.set("已完成" if ok else "已停止")
        self.log(msg)

    # ---------------- 主流程 ----------------
    def _run(self, src, c):
        """所有模式共用 run_pipeline；这里只负责把回调搬到 UI 线程。"""
        try:
            res = run_pipeline(src, c["last_out"], c,
                               log=lambda m: self.ui(self.log, m),
                               progress=lambda d, t: self.ui(self._progress, d, t),
                               cur=lambda s: self.ui(self.cur_text.set, s),
                               gate=self._gate)
        except Exception as e:
            import traceback
            traceback.print_exc()
            self.ui(self._finish, False, f"出错：{type(e).__name__}: {e}")
            return
        task = (res or {}).get("task", "") or ""
        if task:
            self.last_dir = task
        if res.get("stopped"):
            self.ui(self._finish, False, res.get("msg", "已停止"))
            return
        if not res.get("ok"):
            self.ui(self._finish, False, res.get("msg", "失败"))
            return
        self.ui(self._progress, 100, 100)
        self.ui(self.stat_text.set, res.get("stat", ""))
        self.ui(self._finish, True, res.get("msg", "完成"))
        try:
            os.startfile(task)
        except Exception:
            pass

    def _progress(self, done, total):
        self.progress.set(done * 100.0 / max(total, 1))


def main():
    root = tk.Tk()
    app = ChapterSplitterApp(root)

    def on_close():
        if app.running:
            if not messagebox.askyesno("正在运行", "任务还在跑，确定退出吗？"):
                return
            app.stop_event.set()
            app.run_event.set()
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_close)
    root.mainloop()


if __name__ == "__main__":
    main()
