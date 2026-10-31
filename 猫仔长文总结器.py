#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
猫仔长文总结器 v1.5.1
====================
把「事件行 → 素材句 → 场景 → 文学短文」这套工作流做成独立程序：
  每章：① 事件行（时间/地点/人物/权重，可核验的事实骨架）
        ①.5 人称：程序判第一/第三人称；第一人称先定「我」是谁（叙述者.json，全书一次），
             事件行的「我」一律映射成叙述者的名字，第三人称段落单独标出
        ② 素材句（程序从原文分箱摘的短句，带原文位置百分比，供化用细节与台词）
        ③ 场景（程序按地点把事件行聚成 3–6 场，避免短文写成逐条清单）
        ③.5 人物身份先行：先定性别/辈分/亲缘（吃原文证据＋台账＋人物关系册），
             与关系册冲突就回原文数证据，证据不足则沿用前文；正文以此为准
        ④ 文学短文（成品：第三方写作；开头承接上一张卡的落点，结尾落点交给下一张卡；
           权重≥0.6 的事实列入「必须写到」；称谓与已核验身份不一致会被判错重写）
        ⑤ 台账（人物/势力/地点/物品/设定，TSV 增量填表，写完自动加载给下一章当背景）
  每 N 章：结算卡（含祖辈提要，供长程连贯；人物简介取自关系册）
能力：自定义 API / 自定义普通卡与结算卡字数范围 / 实时进度 / 暂停·继续·停止 / 断点续跑
背景与设置存 long_summary_config.json；产出目录结构：
  cards/<源文件名>.md（卡片：文件名→人物简介→正文） cards/<源文件名>.events.md（事件行）
  base/0010.md（结算卡）
  ledger/ch_0001.tsv（本章台账） 全书台账.md 人物关系.json/.md  verify/ 全书总结.md
"""

import os
import re
import json
import time
import threading
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog
from difflib import SequenceMatcher

try:
    import requests
except Exception:
    requests = None

APP_TITLE = "猫仔长文总结器 v1.5.1"
CJK = re.compile(r"[\u4e00-\u9fff]")
QUOTED = re.compile(r"[「“]([^」”]{2,40})[」”]")
EV_LINE = re.compile(
    r"^\s*(\d+)\s*[.:：、)）]\s*[（(\[【]?\s*(.*?)\s*[）)\]}】]\s*(.+?)\s*[（(]\s*"
    r"(?:权重\s*[:：]?\s*)?(0?\.\d+|1\.0+|0|1)\s*[）)]\s*$")
CH_HEAD = re.compile(r"^[\s\u3000]*(第\s*[0-9零〇一二两三四五六七八九十百千万]{1,9}\s*[章节回])")

SYS_EVENTS = (
    "你是小说事实提取器。把本章正文拆成最小事件单元，只记录原文发生的动作、变化、信息。\n"
    "输出 {n} 行，每行严格如下格式，不要别的话：\n"
    "序号: (时间: X | 地点: Y | 人物: A,B) 事件描述 (权重)\n"
    "1) 描述客观具体：谁做了什么、结果如何；不写心理、不写评价、不写悬念。\n"
    "2) 时间地点不明写「未明」，括号不能省。人名照抄原文。\n"
    "3) 权重按 10 维累加（每维 0.05–0.15）封顶 1.0，写成 0.85。\n"
    "4) 时间只写原文的具体时点（清晨／次日／三日后），不要写「序章开场」「对话中」这类流程标签；\n"
    "   地点写到房间或区域这一级；人物栏只写人名，不写组织、不写「众人」「男子」这类泛称。\n"
    "5) 不写「某某心理活动」「背景交代」「场景描述」这类概括行——那不是事件，删掉。\n"
    "示例：3: (时间: 次日清晨 | 地点: 酒店房间 | 人物: 孙元一,关珊雪) 孙元一发现手机被拉黑，"
    "与关珊雪争执后决定回国 (0.75)\n")

STYLE_RULES = {
    "混合": "以写意为主——写氛围、感官、人物的反应与停顿；关键转折处允许一两句直陈，"
            "但不许罗列器官、不许连续铺陈动作序列。",
    "写意": "全程写意——只用氛围、感官、人物的反应与停顿来暗示，不直陈身体动作。",
    "写实": "按原文直陈动作与过程，但不堆砌形容词，保持叙述节制。",
}

# 引语策略：转述最干净（9B 常把真台词往后续写），需要原文语感时才开引语
QUOTE_RULES = {
    "转述": "人物开口一律转述（“他问她能不能陪她去”），全篇不许出现引号台词；"
            "原文的对话改写成间接引语。",
    "允许2处": "人物开口优先转述（“他问她……”）。确需原样引语时，必须从【素材句】里逐字照抄"
               "一整句，不许改字、不许拼接、不许往后面续写；整章至多 2 处，"
               "且要紧贴它在原文所属的那个场面。",
    "宽松": "人物开口可原样引用原文台词（每个引号 5 字以上），但必须逐字照抄【素材句】里的一整句，"
            "不许改字、不许拼接、不许往后面续写。",
}
QUOTE_MAX = {"转述": 0, "允许2处": 2, "宽松": 9}
MIN_QUOTE_CJK = 6   # 不足 6 个汉字的引号内容不当作台词核验（多半是术语/碎片）

SYS_PROSE = (
    "你是小说编者。把给定的一章写成一篇克制的第三人称小叙事，要能和前后两张卡接得上。\n"
    "【叙事要求】\n"
    "1) 贴住本章的主人物，第三人称、过去时；一条主线按因果往下走，不在场面之间乱跳。\n"
    "2) 开头必须承接：先用一两句把处境接上（上一件事的后果、人此刻在哪、时间怎么过去），"
    "再进入本章第一个场面；【上一张卡的结尾】里那个人／那件事要被接着往下写——"
    "可以提一次名字、或借它最后半句起笔，但不许整句照抄、不许整段复述上一章。\n"
    "3) 结尾必须落点：最后一句写清本章结束时谁在哪、什么变了（处境或关系），供下一张卡接着写；"
    "不许用悬念句、不许用“此后……”。\n"
    "4) 覆盖：标了【本章必须写到】的事实一条都不许漏；宁可各用一句，也不要只挑其中几件来写。\n"
    "5) 按权重取舍：重要度≥0.6 详写；0.4–0.6 一笔带过；<0.4 合并成一句或整句略去。"
    "同类的到场、入座、寒暄、衣着合并成一句概括，绝不逐条排。\n"
    "6) 禁止清单式罗列（“某人做了A；某人做了B；某人又做了C”）。同一场面的多个动作要串成"
    "一条连贯的动作链，用停顿、感官、人物反应来过渡；换场面时要有时间或空间的过渡句。\n"
    "7) 只写一条主线；确有多处并行场面时只保留与主线相关的那部分，其余用一句话交代。\n"
    "8) {quotes}\n"
    "9) 不写评价、不写伏笔、不写“接下来会怎样”、不写作者议论。\n"
    "10) 笔法：{style}\n"
    "11) 篇幅 {lo}～{hi} 个汉字（目标 {mid}），宁短勿注水；分 2～4 段；直接给正文，"
    "不要标题、不要小标题、不要任何标签，也不要写人物表（人物简介由程序另附）。\n"
    "12) 玩笑与情趣里的自称（继母笑着自称「女儿」、主人自称「爸爸」）只当床上的叫法，"
    "不许写成真实亲缘，也不许据此改动人物身份；身份一律照【人物身份】。\n"
    "13) {narr}\n"
    "【材料用法】\n"
    "- 场景事件：本章事实骨架。只能用它的事实，不许新增人物、地点、因果。\n"
    "- 素材句：原文细节与台词；方括号里的百分比是它在原文中的位置，引用要放进对应位置的场面。\n"
    "- 上一张卡的结尾：那是紧接本章之前的处境，只用来起笔承接，不得复述、不得当成本章内容。\n"
    "- 前文／台账：只用于人物关系、称谓与承接，不得复述为本章内容、不得当成本章发生的事。\n")

# 人物档案：先定身份，再写一句简介。身份是正文的硬约束
SYS_CAST = (
    "你是小说资料员。第一步先把人物身份定死，第二步才写一句话简介。每行一个人，"
    "格式严格为：姓名｜身份＋简介\n"
    "1) 定身份的证据优先级：①【原文证据】里的原句 ② 台账里的身份／状态 ③ 上一张卡的人物简介。"
    "三者冲突时，以原文证据为准。\n"
    "2) 身份必须写清三件事：性别、辈分／亲缘（谁的儿子、谁的姐姐、谁的妻子）、身份或阵营。"
    "性别或辈分拿不准就写「关系未明」，绝对不许猜——儿子／女儿、哥哥／姐姐、弟弟／妹妹、"
    "父亲／母亲、丈夫／妻子这五对里，写反一个就算错。\n"
    "3) 简介不超过 {hz} 个汉字：先关系身份，再一句本章在做什么或变成什么样。\n"
    "   例：裴青玉｜裴万钧的女儿、裴轩同父异母的姐姐，四阶女修；本章讥讽兄长后上楼。\n"
    "4) 人名照抄输入，不许改名、不许新增没出现的人；最多 {n} 行，按重要度从高到低排。\n"
    "5) 只输出这些行，不要表头、不要编号、不要解释。\n"
    "6) 情趣、玩笑、角色扮演里的自称不算身份：床上叫「爸爸」「女儿」「哥哥」是角色的叫法，"
    "不是真亲缘；只认叙述句和原文的明确交代。前文关系册已经定下的身份，"
    "除非原文叙述明确改变，否则照旧。\n")

# 叙事人称与「我」的归属：全书只判一次
SYS_NARR = (
    "你是小说资料员。读开头的正文，回答两件事：这段文字是什么叙事人称；若是第一人称，「我」是谁。\n"
    "只输出三行，不要解释：\n"
    "人称: 第一人称｜第三人称\n"
    "叙述者: 原文里其他人物对「我」最常用的那个称呼（如「弟弟」「阿明」「大少爷」），2–4 字；"
    "原文确实没人称呼他，就写「主角」\n"
    "证据: 「从原文逐字抄的一句」\n"
    "规则：①台词里的「我」不算，只看叙述句里做主语的那个人；②不许写原文没出现过的名字；\n"
    "③不许把「我／我们」本身写成叙述者——那只是代词；④不要因为「我」提过某人就把他当叙述者。\n")

# 五对互斥称谓：正文里出现相反的那个就算写反了
SYS_BASE = (
    "你是小说史官，把一段事件行合集写成一张文学化的结算卡。只根据输入写，不创作。\n"
    "输入每行：序号: (时间|地点|人物) 事件描述 (权重)，权重代表重要性。\n"
    "输出顺序固定：\n"
    "【祖辈提要】把旧提要（若有）浓缩到 {ti} 字内，只留对后文仍有意义的事实；"
    "输入为“无”时照写“无（本书起始段）”\n"
    "【时间跨度】起止\n【落点】本段结束时的处境，一句话\n"
    "【本段记录】按时间顺序写成连贯叙事：权重>0.6 的事件详写，<0.3 可合并或省略；"
    "不许罗列条目、不许逐条复述；笔法同章卡；整卡 {lo}～{hi} 个汉字\n"
    "不写悬念、不写伏笔、不写展望、不写评价。")

# 台账：以「人物 × 章节」为坐标系填表，后文按人物或章号秒查
LEDGER_CATS = ("人物章", "势力", "地点", "物品", "设定")

SYS_TABLE = (
    "你是小说资料员。为本章填一张要素台账，日后要按人物或章节查「谁在第几章变成了什么样」。\n"
    "只输出 TSV，每行 7 列，用制表符分隔，不要表头、不要解释、不要代码块：\n"
    "分类\t名称\t别名\t身份\t地点\t状态\t重要度\n"
    "1) 分类只能是这五个词之一：人物章 / 势力 / 地点 / 物品 / 设定。"
    "不许写成「物品章」「设定章」「人物」这类变体。\n"
    "2) 「状态」写本章**结束时**该要素处于什么状态：一句短语，15～30 字，"
    "只写「现在是什么样」，不写它做了什么、不写过程。"
    "例：「被通缉的在逃者」「知情的待决囚徒」「已废的三皇子」「钱家的独女，被当作筹码」。"
    "本章没有变化的要素可以不填；后文仍需要它时补一行，写它当前的样子。\n"
    "3) 人物章只写有名字的人。泛称（男子／众人／狱卒甲）、物品、地点、功法、身体部位"
    "一律不许归到人物章，该归哪类归哪类；本章没有有名字的人出场，人物章一行都不写。\n"
    "4) 别名：只许填本章正文里出现过的其他叫法（小名、称号、昵称、简称），没有就留空，不许推断。\n"
    "5) 身份只写原文明确给出的身份或阵营（师父／女仆长／中央学院新生），拿不准就留空，不许猜。\n"
    "6) 势力／地点／物品／设定只收后文还用得上的专名，状态写它当前的状态或本章新增的信息。\n"
    "7) 重要度 0.00–1.00，取该要素在本章事件行里的最高权重。列不能少，空的列要留空但保留制表符。\n"
    "示例：人物章\t钱青\t\t中央学院一年生\t诏狱房间\t被当众揭破家变的天真少年 → 知情的待决囚徒\t0.95\n")

DEFAULT_CFG = {
    "api_url": "http://127.0.0.1:19093/v1/chat/completions",
    "api_key": "",
    "model": "qwen3.6-35b-a3b",
    "timeout": 600,
    "temp": 0.5,
    "card_lo": 400, "card_hi": 800,
    "base_lo": 900, "base_hi": 3200,
    "settle_every": 10,
    "ev_max": 12,
    "material": 8,
    "attempts": 3,
    "style": "混合",
    "quote_mode": "转述",
    "cast_enable": True,
    "cast_n": 6,
    "cast_hz": 50,
    "narrator": "",
    "out_dir": "",
    "rewrite": False,
}


REL_PAIRS = (("儿子", "女儿"), ("哥哥", "姐姐"), ("兄长", "姐姐"), ("弟弟", "妹妹"),
             ("父亲", "母亲"), ("丈夫", "妻子"), ("师父", "师娘"))
REL_WORDS = tuple({w for p in REL_PAIRS for w in p}) + ("爸爸", "妈妈", "妹子", "兄弟")
# 带持有者的亲缘：「裴万钧的女儿」→ (裴万钧, 女儿)。同一对 (持有者, 当事人) 只能有一种亲缘
REL_ALL = ("儿子", "女儿", "哥哥", "姐姐", "兄长", "弟弟", "妹妹", "父亲", "母亲",
           "丈夫", "妻子", "未婚妻", "未婚夫", "师父", "师娘", "妾",
           "继母", "继父", "养母", "养父", "岳母", "岳父", "儿媳", "女婿", "嫂子", "姐夫", "妹夫")
HOLDER_RE = re.compile(r"([\u4e00-\u9fff]{2,4})[之的](" + "|".join(REL_ALL) + ")")
SELF_RE = re.compile(r"(?:是|为|乃|作为|身为)(" + "|".join(REL_ALL) + ")")
SELF_HOLDER_RE = re.compile(r"(?:是|为|乃|作为|身为)([\u4e00-\u9fff]{2,4})[之的]("
                            + "|".join(REL_ALL) + ")")
# 文言式说法统一成「X的Y」，后面所有正则都能吃到
WENYAN = {"之妻": "的妻子", "之父": "的父亲", "之女": "的女儿", "之子": "的儿子",
          "之母": "的母亲", "之兄": "的哥哥", "之姐": "的姐姐", "之弟": "的弟弟",
          "之妹": "的妹妹", "之夫": "的丈夫", "之妾": "的妾", "乃": "是"}


def norm_rel(t):
    s = str(t or "")
    for a, b in WENYAN.items():
        s = s.replace(a, b)
    return s


def rel_triples(txt, names):
    """叙述里带持有者的亲缘 {(持有者, 当事人): 亲缘}。

    持有者只认「已知人名」，避免把「同父异母」「与裴青玉」这类修饰当成持有者；
    引号里的台词与玩笑句不计。
    """
    out = {}
    t = drop_joke(norm_rel(strip_dialog(txt)))
    names = [n for n in (names or ()) if n]
    if not names:
        return out
    alt = "|".join(re.escape(x) for x in sorted(names, key=len, reverse=True))
    rels = "|".join(REL_ALL)
    for subj in names:
        for m in re.finditer(re.escape(subj), t):
            back = t[max(0, m.start() - 18):m.start()]
            mm = re.search("(" + alt + r")[^，。；]{0,4}?[之的](" + rels + ")$", back)
            if mm and mm.group(1) != subj:
                out.setdefault((mm.group(1), subj), set()).add(mm.group(2))
            fwd = t[m.end():m.end() + 20]
            mf = re.match(r"\s*(?:是|为|乃|作为|身为)(" + alt + r")[之的](" + rels + ")", fwd)
            if mf and mf.group(1) != subj:
                out.setdefault((mf.group(1), subj), set()).add(mf.group(2))
    return out


def id_triples(id_rows):
    """人物档案 → {(持有者, 当事人): 亲缘}。档案里「裴万钧之女」即当事人是持有者的女儿。"""
    out = {}
    all_names = [x for x, _ in (id_rows or ())]
    for n, d in id_rows or ():
        head = re.split(r"[；;]", str(d or ""))[0]
        head = re.sub(r"[（(【\[][^）)】\]]{0,40}[）)】\]]", "", head)
        head = drop_joke(norm_rel(strip_dialog(head)))
        for (h, s), rels in rel_triples(head, all_names).items():
            if s == n:
                out.setdefault((h, n), set()).update(rels)
        # 「裴轩异母姐姐」这种省了「的/之」的写法：已知人名 + ≤6 字 + 亲缘词
        for nm in all_names:
            if nm == n:
                continue
            for m in re.finditer(re.escape(nm), head):
                tail = head[m.end():m.end() + 8]
                mr = re.match(r"[^，、；。]{0,6}?(" + "|".join(REL_ALL) + ")", tail)
                if mr:
                    out.setdefault((nm, n), set()).add(mr.group(1))
    return out


def triple_support(holder, name, word, text):
    """回原文数证据：「X的Y」这种带持有者的写法出现几次（引号与玩笑句已剔除）。"""
    t = drop_joke(norm_rel(strip_dialog(text)))
    if not holder or not word:
        return 0
    return len(re.findall(re.escape(holder) + r"\s*[之的]\s*" + re.escape(word), t))



def declared_rels(id_rows):
    """人物档案 → {名: 声明称谓集合}。

    只认身份段（第一个分号之前），去掉括号里的注解，也不采信玩笑/自称。
    """
    out = {}
    for n, d in id_rows or ():
        head = re.split(r"[；;]", str(d or ""))[0]
        head = re.sub(r"[（(【\[][^）)】\]]{0,40}[）)】\]]", "", head)   # 去掉（本章自称…）这类注解
        head = drop_joke(norm_rel(strip_dialog(head)))
        got = rel_claims(head, [n]).get(n) or set()
        for w in REL_WORDS:
            if w in head:
                got.add(w)
        if got:
            out[n] = got
    return out


def rel_support(name, words, text, win=30):
    """回原文数证据：名字前后 win 字内，各称谓词各出现几次。"""
    t = str(text or "")
    score = {}
    for m in re.finditer(re.escape(name), t):
        seg = t[max(0, m.start() - win):m.end() + win]
        for w in words:
            if w in seg:
                score[w] = score.get(w, 0) + 1
    return score





NAME_HEAD = "一二三四五六七八九十两几众数多每各某"
NAME_BAD = "人们者家属子女男"
# 模型常拿这些词当「人物」占位，不能当人名去全书检索
NAME_STOP = {"未明", "不明", "未知", "未详", "不详", "未定", "无名", "未记", "略", "无",
             "我", "我们", "咱们", "咱", "俺", "本人", "自己", "主角", "叙述者", "笔者"}
# 角色/关系词：不是人名，不许进人物表（模型爱把它们当人物）
NAME_GENERIC = {"系统", "管家", "前妻", "后妈", "继母", "母亲", "父亲", "姐姐", "妹妹",
                "哥哥", "弟弟", "儿子", "女儿", "丈夫", "妻子", "师父", "徒弟", "老爷",
                "夫人", "少爷", "小姐", "侍女", "仆人", "下人", "老者", "老头", "妇人",
                "少女", "少年", "男人", "女人", "男子", "女子", "众人", "对方", "两人",
                "三人", "老师", "校长", "医生", "护士", "司机", "老板", "店主", "掌柜"}
NAME_DESC = ("陌生", "年轻", "中年", "老年", "少年", "少女", "老头", "老者", "妇人", "众人")
# 「裴母／裴父／长孙氏」这类缩写称呼：不是编造，也不是正式人名
ROLE_TAIL = set("母父妻夫妹姐哥弟氏家")


def looks_like_name(s):
    """2–3 字且不像「两男子/众人/家属」这类描述词，才当人名去查。"""
    s = (s or "").strip()
    if s in NAME_STOP:
        return False
    if not (1 < len(s) <= 3):
        return False
    if s[0] in NAME_HEAD:
        return False
    if any(c in s for c in NAME_BAD):
        return False
    return True


CAT_ALIAS = {"人物": "人物章", "角色": "人物章", "人": "人物章"}
NAMED_CATS = ("势力", "地点", "物品", "设定")


def norm_cat(cat):
    """把模型自创的分类钳到 5 个合法值；归一不了就返回空串（该行丢弃）。"""
    c = re.sub(r"\s+", "", cat or "")
    if c in LEDGER_CATS:
        return c
    if c in CAT_ALIAS:
        return CAT_ALIAS[c]
    if len(c) == 3 and c[:-1] in NAMED_CATS:      # 物品章／设定章／地点章／势力章
        return c[:-1]
    return ""


OBJ_TAIL = set("牌锁纹袜衣架剑刀枪囊珠印令丹符镯簪杖弓甲袍裙靴绳链盒瓶壶琴棋桌椅门窗墙"
               "罐杯盏镜鼎炉卷册幡旗鼓帕巾冠履钗屏榻枕席室房营场区界域")
LOC_TAIL = set("街道城宫殿阁楼院府山河湖林谷洞岛村镇京州郡县港关塔寺庙馆栈苑园冢墓滩峡窟")
ORG_TAIL = set("局部司厅会团队宗门派族帮社组署衙")
OBJ_TAIL |= LOC_TAIL | ORG_TAIL
NAME_BAD2 = set("众男女子们家属人者员伢厮婢仆兵卒役")


def person_ok(name, ev_names=(), ledger_names=()):
    """人物章这行是不是「真的人」——排除式：只丢明确的器物/地名/组织/泛称，宁可放过人名。"""
    n = (name or "").strip()
    if not (1 < len(n) <= 4):
        return False
    if n in ledger_names or n in ev_names:      # 事件行或台账已经把它当人 → 放行
        return True
    if n[0] in NAME_HEAD or any(c in n for c in NAME_BAD):
        return False
    return not (n[-1] in OBJ_TAIL or n[-1] in NAME_BAD2)


def is_person_name(n):
    """够不够格当「人物表里的人名」：排除泛称、角色词、器物地名、缩写称呼。"""
    n = (n or "").strip()
    if n in NAME_STOP or n in NAME_GENERIC:
        return False
    if any(w in n for w in NAME_DESC):
        return False
    if not (1 < len(n) <= 4):
        return False
    if n[-1] in ROLE_TAIL:
        return False
    if n[0] in NAME_HEAD or any(c in n for c in NAME_BAD):
        return False
    return not (n[-1] in OBJ_TAIL or n[-1] in NAME_BAD2)


def n_hz(s):
    return len(CJK.findall(s or ""))


def cjk_only(s):
    return re.sub(r"[^\u4e00-\u9fff]", "", s or "")


CAST_HEAD = "【本章重要人物】"


# ==================== 叙事人称：「我」到底是谁 ====================
# 第一人称书里，「我」是叙述者；但情趣台词里的「我」、玩笑里的自称不算。
# 判据看口吻（我与心理动词密度），不能只看「有没有我」——交代背景的段落常不带我。
NARR_WORDS = {"我", "我们", "咱们", "咱", "俺", "本人", "自己", "主角", "叙述者", "笔者"}
PSYCH = ("想", "觉得", "心里", "暗自", "心想", "琢磨", "以为", "感到", "担心",
         "记得", "明白", "反应过来", "寻思")


def iter_paras(t):
    """按空行或「　　」缩进切段：txt 多是 40 字硬换行，按行算段落会全错。"""
    out, buf = [], []
    for ln in (t or "").split("\n"):
        s = ln.strip()
        if not s:
            if buf:
                out.append("".join(buf))
                buf = []
            continue
        if buf and (ln.startswith("\u3000\u3000") or ln.startswith("\t") or ln.startswith("  ")):
            out.append("".join(buf))
            buf = [s]
        else:
            buf.append(s)
    if buf:
        out.append("".join(buf))
    return out


def count_me(t):
    """叙述用的「我」：台词里的不算（「我还在放寒假」是人物说话，不是叙述者动作）。"""
    return sum(strip_dialog(t or "").count(w) for w in ("我", "咱", "俺"))


def detect_pov(text):
    """判一段正文的叙事人称，并挑出真正的第三人称段落。

    first：我/每千字 ≥2；third：我稀薄且他/她为主；mixed：两者都有。
    第三人称段落＝≥80 字、没有「我」、有心理动词、他/她 ≥2 —— 只是交代背景不算。
    """
    body = strip_dialog(text or "")
    cj = max(1, n_hz(body))
    me = count_me(body)
    third = body.count("他") + body.count("她")
    per1k = me * 1000.0 / cj
    spans, pos, total = [], 0, max(1, len(text or ""))
    for para in iter_paras(text):
        pos += len(para)
        body_p = strip_dialog(para)                 # 只看叙述：整段都是台词的不算第三人称段
        if len(body_p) < 60 or count_me(body_p):
            continue
        if (body_p.count("他") + body_p.count("她")) < 2:
            continue
        if not any(w in body_p for w in PSYCH):
            continue
        spans.append((int(pos * 100 / total), body_p[:40]))
    ratio = sum(len(s[1]) for s in spans) * 1.0 / total
    if per1k >= 2.0:
        verdict = "mixed" if ratio >= 0.12 else "first"
    elif per1k >= 0.6:
        verdict = "mixed"
    else:
        verdict = "third"
    return {"verdict": verdict, "me": me, "third": third, "per1k": round(per1k, 2),
            "spans": spans[:4], "span_ratio": round(ratio, 3)}


def guess_narrator(text, topn=6):
    """与「我」同段、且反复出现的称呼——只是给模型的候选，最后要模型+原文核验。

    n-gram 会产出大量「出来／然后就」这类垃圾，用停用字 + 出现次数 + 跨段数过滤。
    """
    BADCH = set("的了是在和就不都也还很太更又没要有会能可这那你我他她它们个把被让给对从到"
                "上下里外中说着过做去来想看得地儿吧呢啊呀么什怎样些点次天时后前年日月")
    score, paras_of = {}, {}
    for pi, para in enumerate(iter_paras(text or "")):
        if not count_me(para):
            continue
        for nm in set(re.findall(r"[\u4e00-\u9fff]{2,3}", para)):
            if nm in NARR_WORDS or nm in NAME_STOP or not is_person_name(nm):
                continue
            if any(c in BADCH for c in nm):
                continue
            score[nm] = score.get(nm, 0) + 1
            paras_of.setdefault(nm, set()).add(pi)
    keep = [(n, k) for n, k in score.items()
            if (k >= 4 and len(n) == 2) or (k >= 3 and len(n) == 3)]
    keep.sort(key=lambda kv: (-kv[1], -len(paras_of.get(kv[0], ()))))
    return keep[:topn]


def map_me(txt, name):
    """把叙述里的「我／我们／咱／俺」换成叙述者的名字；引号里的台词一个字不动。"""
    if not name or not txt:
        return txt
    chunks = re.split(r"(「[^」]*」|『[^』]*』|“[^”]*”)", txt)
    for i, seg in enumerate(chunks):
        if seg.startswith(("「", "『", "“")):
            continue
        chunks[i] = (seg.replace("我们", name).replace("咱们", name)
                     .replace("咱", name).replace("俺", name).replace("我", name))
    return "".join(chunks)


def rows_text(rows):
    """把事件行渲染回文本：落盘用这个版本（「我」已换成叙述者的名字）。"""
    return "\n".join(f"{r['idx']}: ({r['ctx']}) {r['desc']} ({r['w']:.2f})" for r in rows)


def split_card(txt):
    """卡片文件 = 「# 标题」+ 人物块 + 正文。返回 (正文, 人物块)。

    人物块在开头（新格式）或结尾（老卡）都能认；没有块就返回 (去标题的全文, '')。
    """
    lines = str(txt or "").split("\n")
    if lines and lines[0].startswith("# "):      # 第一行是卡片标题＝源文件名
        lines = lines[1:]
    try:
        i = next(k for k, l in enumerate(lines) if l.strip().startswith(CAST_HEAD))
    except StopIteration:
        return "\n".join(lines).strip(), ""
    j = i + 1
    while j < len(lines) and lines[j].strip() and not lines[j].startswith("# "):
        j += 1
    cast = "\n".join(lines[i:j]).strip()
    prose = "\n".join(lines[:i] + lines[j:]).strip()
    return prose, cast


def safe_stem(s, fallback="card"):
    """源文件名 / 章节名 → 安全文件名主干（保留中文与 _-，去掉扩展名）。"""
    s = re.sub(r"\.(txt|md|TXT|MD)$", "", str(s or ""))
    s = re.sub(r'[\\/:*?"<>|\s]+', "_", s).strip("._ ")
    s = re.sub(r"_+", "_", s)
    return s[:80] or fallback


def card_text(stem, id_rows, prose):
    """卡片正文：标题（＝文件名）→ 人物简介 → 总结正文。"""
    parts = [f"# {stem}", ""]
    blk = cast_block(id_rows)
    if blk:
        parts += [blk, ""]
    parts.append(str(prose or "").strip())
    return "\n".join(parts).rstrip() + "\n"


def trim_hz(s, hz):
    """把一句话截到 hz 个汉字以内，尽量断在标点。"""
    s = re.sub(r"\s+", "", str(s or ""))
    if n_hz(s) <= hz:
        return s
    pos, n = None, 0
    for i, ch in enumerate(s):
        if CJK.match(ch):
            n += 1
            if n >= hz:
                pos = i + 1
                break
    cut = s[:pos] if pos else s
    m = re.search(r"^(.*[。！？；，、])[^。！？；，、]*$", cut)
    if m and n_hz(m.group(1)) >= max(8, hz // 2):
        return m.group(1)
    return cut.rstrip("，、；：,;:") + "…"


def parse_cast(raw, hz=50, maxn=8):
    """把模型回的人物行解析成 [(姓名, 简介)]：去重、限长、限人数。"""
    out, seen = [], set()
    for ln in str(raw or "").split("\n"):
        s = ln.strip()
        s = re.sub(r"^[-–—*·•\s]+", "", s)
        s = re.sub(r"^\d+[.、)）]\s*", "", s)
        if not s or CAST_HEAD in s or s.startswith("【") or s.startswith("姓名"):
            continue
        sep = None
        for c in ("｜", "|", "：", ":"):
            if c in s:
                sep = c
                break
        if not sep:
            continue
        nm, one = s.split(sep, 1)
        nm = nm.strip().strip("（）()【】[]「」\"'“” ")
        one = one.strip().strip("（）()")
        if not (1 < len(nm) <= 6) or not one:
            continue
        if nm in seen:
            continue
        one = trim_hz(one, hz)
        if n_hz(one) < 6:
            continue
        seen.add(nm)
        out.append((nm, one))
        if len(out) >= maxn:
            break
    return out


def cast_block(rows):
    if not rows:
        return ""
    return CAST_HEAD + "\n" + "\n".join(f"- {n}：{t}" for n, t in rows)


REL_HINT = ("儿子", "女儿", "哥哥", "姐姐", "兄长", "弟弟", "妹妹", "父亲", "母亲",
            "丈夫", "妻子", "未婚妻", "未婚夫", "师父", "妾", "夫人", "小姐", "少爷")
# 玩笑 / 情趣 / 角色扮演语境：这些句子里的自称不算真实身份
JOKE_HINT = ("玩笑", "打趣", "调笑", "戏称", "自称", "装作", "假装", "撒娇", "娇声", "娇嗔",
             "嘻笑", "逗弄", "逗她", "逗他", "情趣", "角色扮演", "故作", "亲昵", "昵称",
             "玩闹", "打闹", "叫床", "娇笑", "戏谑", "调侃", "坏笑", "媚声", "娇唤", "声称")
DIALOG_RE = re.compile(r"[「“『\"]([^」”』\"]{0,300})[」”』\"]")


def strip_dialog(t):
    """去掉引号里的台词/自称——台词是人物在说话，不是叙述在定性。"""
    return DIALOG_RE.sub("", str(t or ""))


def drop_joke(t):
    """去掉带玩笑/情趣语境的片段（按句、逗号切）。"""
    out = []
    for seg in re.split(r"[。！？；\n，,]", str(t or "")):
        if not seg.strip():
            continue
        if any(w in seg for w in JOKE_HINT):
            continue
        out.append(seg)
    return "，".join(out)


def relation_evidence(names, text, per_name=2, limit=1500):
    """从原文里摘「人名 + 亲缘词」的叙述句，作为定身份的第一手证据。

    引号里的台词、玩笑/情趣语境的句子一律不作证据。
    """
    out, used = [], set()
    text = str(text or "")
    spans = [(m.start(), m.end()) for m in DIALOG_RE.finditer(text)]

    def in_dialog(pos):
        return any(a <= pos < b for a, b in spans)

    for nm in names or ():
        got = 0
        for m in re.finditer(re.escape(nm), text):
            if in_dialog(m.start()):
                continue
            seg = text[max(0, m.start() - 30):m.end() + 30].replace("\n", " ")
            if not any(w in seg for w in REL_HINT):
                continue
            if any(w in seg for w in JOKE_HINT):
                continue
            seg = re.sub(r"\s+", " ", seg).strip()
            if seg in used:
                continue
            used.add(seg)
            out.append(f"- {nm}：…{seg}…")
            got += 1
            if got >= per_name:
                break
        if sum(len(x) for x in out) > limit:
            break
    return "\n".join(out)[:limit]


def rel_claims(txt, names):
    """正文里「某人被安上的亲缘称谓」→ {名: {称谓}}。只认叙述、只认紧邻用法。"""
    out = {}
    t = drop_joke(norm_rel(strip_dialog(txt)))
    for nm in names or ():
        got = set()
        for m in re.finditer(re.escape(nm), t):
            before = t[max(0, m.start() - 8):m.start()]
            after = t[m.end():m.end() + 10]
            for w in REL_WORDS:
                if re.search(re.escape(w) + r"[，、]?\s*(?:名叫|叫|就是|是)?\s*(?:他|她)?(?:的)?\s*$",
                             before):
                    got.add(w)
                if re.match(r"\s*(?:是|为|乃|作为|身为)?\s*(?:他|她)?(?:的)?\s*" + re.escape(w), after):
                    got.add(w)
        if got:
            out[nm] = got
    return out


def rel_conflict(declared, claimed):
    """返回写反的称谓对（声明里是正面词，正文用了反面词）。"""
    bad = []
    for a, b in REL_PAIRS:
        if (a in declared and b in claimed) or (b in declared and a in claimed):
            bad.append(f"{a}↔{b}")
    return bad


def cfg_path():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), "long_summary_config.json")


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


def norm_url(u):
    u = (u or "").strip().rstrip("/")
    if not u:
        return u
    if u.endswith("/chat/completions"):
        return u
    if u.endswith("/v1"):
        return u + "/chat/completions"
    return u + "/v1/chat/completions"


class LongSummaryApp:
    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.cfg = load_cfg()

        self.src_path = tk.StringVar(value="")
        self.out_dir = tk.StringVar(value=self.cfg.get("out_dir", ""))
        self.api_url = tk.StringVar(value=self.cfg.get("api_url", ""))
        self.api_key = tk.StringVar(value=self.cfg.get("api_key", ""))
        self.model = tk.StringVar(value=self.cfg.get("model", ""))
        self.timeout = tk.StringVar(value=str(self.cfg.get("timeout", 600)))
        self.temp = tk.StringVar(value=str(self.cfg.get("temp", 0.5)))
        self.card_lo = tk.StringVar(value=str(self.cfg.get("card_lo", 200)))
        self.card_hi = tk.StringVar(value=str(self.cfg.get("card_hi", 800)))
        self.base_lo = tk.StringVar(value=str(self.cfg.get("base_lo", 900)))
        self.base_hi = tk.StringVar(value=str(self.cfg.get("base_hi", 3200)))
        self.settle_every = tk.StringVar(value=str(self.cfg.get("settle_every", 10)))
        self.ev_max = tk.StringVar(value=str(self.cfg.get("ev_max", 12)))
        self.material = tk.StringVar(value=str(self.cfg.get("material", 8)))
        self.attempts = tk.StringVar(value=str(self.cfg.get("attempts", 3)))
        self.style = tk.StringVar(value=self.cfg.get("style", "混合"))
        self.quote_mode = tk.StringVar(value=self.cfg.get("quote_mode", "转述"))
        self.rewrite = tk.BooleanVar(value=bool(self.cfg.get("rewrite", False)))
        self.cast_enable = tk.BooleanVar(value=bool(self.cfg.get("cast_enable", True)))
        self.cast_n = tk.StringVar(value=str(self.cfg.get("cast_n", 6)))
        self.cast_hz = tk.StringVar(value=str(self.cfg.get("cast_hz", 50)))
        self.narrator = tk.StringVar(value=str(self.cfg.get("narrator", "")))

        self.progress = tk.DoubleVar(value=0)
        self.progress_text = tk.StringVar(value="0 / 0")
        self.state_text = tk.StringVar(value="就绪")
        self.cur_chapter = tk.StringVar(value="—")
        self.stat_text = tk.StringVar(value="未开始")

        self.worker = None
        self.stop_event = threading.Event()
        self.run_event = threading.Event()   # set = 运行中；clear = 暂停
        self.running = False
        self.paused = False
        self.api_calls = 0
        self.t_start = 0
        self.last_task_dir = ""

        self._build_ui()
        self.log("程序就绪。选择 txt 或已分章的目录，填好 API，点「开始」。")

    # ============================== 界面 ==============================
    def _build_ui(self):
        root = self.root
        root.geometry("920x790")
        root.grid_columnconfigure(0, weight=1)
        root.grid_rowconfigure(3, weight=1)

        # ---- 输入 / 输出 ----
        f1 = tk.LabelFrame(root, text="① 素材与输出", padx=8, pady=6)
        f1.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 4))
        f1.grid_columnconfigure(1, weight=1)

        tk.Label(f1, text="小说来源:").grid(row=0, column=0, sticky="e")
        tk.Entry(f1, textvariable=self.src_path).grid(row=0, column=1, sticky="ew", padx=4)
        tk.Button(f1, text="选 txt", width=8, command=self.pick_txt).grid(row=0, column=2, padx=2)
        tk.Button(f1, text="选章节目录", width=11, command=self.pick_dir).grid(row=0, column=3, padx=2)

        tk.Label(f1, text="输出目录:").grid(row=1, column=0, sticky="e", pady=4)
        tk.Entry(f1, textvariable=self.out_dir).grid(row=1, column=1, sticky="ew", padx=4)
        tk.Button(f1, text="选择", width=8, command=self.pick_out).grid(row=1, column=2, padx=2)
        tk.Button(f1, text="打开", width=8, command=self.open_out).grid(row=1, column=3, padx=2)

        # ---- API ----
        f2 = tk.LabelFrame(root, text="② API（OpenAI 兼容 /v1）", padx=8, pady=6)
        f2.grid(row=1, column=0, sticky="ew", padx=10, pady=4)
        f2.grid_columnconfigure(1, weight=1)
        for r, (lab, var, show) in enumerate((
                ("地址", self.api_url, ""), ("密钥", self.api_key, "*"),
                ("模型", self.model, ""), ("超时(秒)", self.timeout, ""))):
            tk.Label(f2, text=lab + ":").grid(row=r, column=0, sticky="e")
            tk.Entry(f2, textvariable=var, show=show).grid(row=r, column=1, sticky="ew", padx=4, pady=2)
        bf = tk.Frame(f2)
        bf.grid(row=0, column=2, rowspan=4, padx=6)
        self.btn_test = tk.Button(bf, text="测试连接\n取模型名", width=12, command=self.test_api)
        self.btn_test.pack(pady=2)
        tk.Button(bf, text="保存配置", width=12, command=self.save_all).pack(pady=2)

        # ---- 参数 ----
        f3 = tk.LabelFrame(root, text="③ 卡片参数", padx=8, pady=6)
        f3.grid(row=2, column=0, sticky="ew", padx=10, pady=4)
        for i in range(8):
            f3.grid_columnconfigure(i, weight=1)

        def pair(r, c, lab, a, b):
            tk.Label(f3, text=lab).grid(row=r, column=c, sticky="e", padx=(6, 2))
            tk.Entry(f3, textvariable=a, width=6).grid(row=r, column=c + 1, sticky="w")
            tk.Label(f3, text="～").grid(row=r, column=c + 2)
            tk.Entry(f3, textvariable=b, width=6).grid(row=r, column=c + 3, sticky="w")

        pair(0, 0, "普通卡字数", self.card_lo, self.card_hi)
        pair(0, 4, "结算卡字数", self.base_lo, self.base_hi)
        tk.Label(f3, text="每几章结算").grid(row=1, column=0, sticky="e", padx=(6, 2))
        tk.Entry(f3, textvariable=self.settle_every, width=6).grid(row=1, column=1, sticky="w")
        tk.Label(f3, text="事件行上限").grid(row=1, column=2, sticky="e")
        tk.Entry(f3, textvariable=self.ev_max, width=6).grid(row=1, column=3, sticky="w")
        tk.Label(f3, text="素材句数").grid(row=1, column=4, sticky="e")
        tk.Entry(f3, textvariable=self.material, width=6).grid(row=1, column=5, sticky="w")
        tk.Label(f3, text="重试轮数").grid(row=1, column=6, sticky="e")
        tk.Entry(f3, textvariable=self.attempts, width=6).grid(row=1, column=7, sticky="w")

        tk.Label(f3, text="温度").grid(row=2, column=0, sticky="e", padx=(6, 2))
        tk.Entry(f3, textvariable=self.temp, width=6).grid(row=2, column=1, sticky="w")
        tk.Label(f3, text="笔法").grid(row=2, column=2, sticky="e")
        sf = tk.Frame(f3)
        sf.grid(row=2, column=3, columnspan=5, sticky="w")
        for s in ("混合", "写意", "写实"):
            tk.Radiobutton(sf, text=s, variable=self.style, value=s).pack(side="left", padx=2)

        tk.Label(f3, text="引语策略").grid(row=3, column=0, sticky="e", padx=(6, 2))
        ttk.Combobox(f3, textvariable=self.quote_mode, width=10, state="readonly",
                     values=("转述", "允许2处", "宽松")).grid(row=3, column=1, sticky="w")
        tk.Label(f3, text="转述=不出引号台词（最稳）／允许2处=可逐字引两句／宽松=不限处数",
                 fg="gray").grid(row=3, column=2, columnspan=6, sticky="w")

        tk.Checkbutton(f3, text="每卡附「本章重要人物」", variable=self.cast_enable).grid(
            row=4, column=0, columnspan=2, sticky="w", pady=(4, 0))
        tk.Label(f3, text="每人 ≤").grid(row=4, column=2, sticky="e", pady=(4, 0))
        tk.Entry(f3, textvariable=self.cast_hz, width=6).grid(row=4, column=3, sticky="w", pady=(4, 0))
        tk.Label(f3, text="字　每卡最多").grid(row=4, column=4, sticky="e", pady=(4, 0))
        tk.Entry(f3, textvariable=self.cast_n, width=6).grid(row=4, column=5, sticky="w", pady=(4, 0))
        tk.Label(f3, text="人（1–50，含社会关系；老卡缺这块会自动补，不重写正文）",
                 fg="gray").grid(row=4, column=6, columnspan=2, sticky="w", pady=(4, 0))

        tk.Label(f3, text="叙述者").grid(row=5, column=0, sticky="e", padx=(6, 2), pady=(4, 0))
        tk.Entry(f3, textvariable=self.narrator, width=10).grid(row=5, column=1, sticky="w", pady=(4, 0))
        tk.Label(f3, text="第一人称书里的「我」＝谁；留空＝自动识别（每本书只判一次，存 叙述者.json）",
                 fg="gray").grid(row=5, column=2, columnspan=6, sticky="w", pady=(4, 0))

        # ---- 控制 + 进度 ----
        f4 = tk.LabelFrame(root, text="④ 运行", padx=8, pady=6)
        f4.grid(row=3, column=0, sticky="nsew", padx=10, pady=(4, 10))
        f4.grid_columnconfigure(0, weight=1)
        f4.grid_rowconfigure(3, weight=1)

        bar = tk.Frame(f4)
        bar.grid(row=0, column=0, sticky="ew")
        self.btn_start = tk.Button(bar, text="▶ 开始", width=10, command=self.start)
        self.btn_start.pack(side="left", padx=2)
        self.btn_pause = tk.Button(bar, text="⏸ 暂停", width=10, command=self.toggle_pause, state="disabled")
        self.btn_pause.pack(side="left", padx=2)
        self.btn_stop = tk.Button(bar, text="⏹ 停止", width=10, command=self.stop, state="disabled")
        self.btn_stop.pack(side="left", padx=2)
        tk.Checkbutton(bar, text="重写已有成稿（v1.1 新笔法覆盖旧稿）",
                       variable=self.rewrite).pack(side="left", padx=8)
        tk.Label(bar, textvariable=self.state_text, fg="#2c3e50").pack(side="left", padx=12)
        tk.Label(bar, textvariable=self.stat_text, fg="gray").pack(side="left")

        self.pbar = ttk.Progressbar(f4, variable=self.progress, maximum=100)
        self.pbar.grid(row=1, column=0, sticky="ew", pady=(8, 2))
        info = tk.Frame(f4)
        info.grid(row=2, column=0, sticky="ew")
        tk.Label(info, textvariable=self.progress_text).pack(side="left")
        tk.Label(info, text="  当前：").pack(side="left")
        tk.Label(info, textvariable=self.cur_chapter, fg="#c0392b").pack(side="left")

        self.log_box = scrolledtext.ScrolledText(f4, height=14, font=("Consolas", 9))
        self.log_box.grid(row=3, column=0, sticky="nsew", pady=(6, 0))

    # ============================== 小工具 ==============================
    def log(self, msg):
        t = time.strftime("%H:%M:%S")
        try:
            self.log_box.insert("end", f"[{t}] {msg}\n")
            self.log_box.see("end")
        except Exception:
            pass

    def ui(self, fn, *a):
        self.root.after(0, lambda: fn(*a))

    def pick_txt(self):
        p = filedialog.askopenfilename(title="选择小说 txt", filetypes=[("文本", "*.txt"), ("全部", "*.*")])
        if p:
            self.src_path.set(p)
            if not self.out_dir.get().strip():
                self.out_dir.set(os.path.join(os.path.dirname(p),
                                              os.path.splitext(os.path.basename(p))[0] + "_章节总结"))

    def pick_dir(self):
        p = filedialog.askdirectory(title="选择已分好的章节目录（内含 *.txt）")
        if p:
            self.src_path.set(p)
            if not self.out_dir.get().strip():
                self.out_dir.set(p.rstrip("\\/") + "_章节总结")

    def pick_out(self):
        p = filedialog.askdirectory(title="选择输出目录")
        if p:
            self.out_dir.set(p)

    def open_out(self):
        p = getattr(self, "last_task_dir", "") or self.out_dir.get().strip()
        if p and os.path.isdir(p):
            os.startfile(p)
        else:
            messagebox.showinfo("提示", "输出目录还没创建（开始运行后自动创建）")

    def collect(self):
        try:
            c = {
                "api_url": norm_url(self.api_url.get()),
                "api_key": self.api_key.get().strip(),
                "model": self.model.get().strip(),
                "timeout": int(float(self.timeout.get() or 600)),
                "temp": float(self.temp.get() or 0.5),
                "card_lo": int(float(self.card_lo.get() or 200)),
                "card_hi": int(float(self.card_hi.get() or 800)),
                "base_lo": int(float(self.base_lo.get() or 900)),
                "base_hi": int(float(self.base_hi.get() or 3200)),
                "settle_every": int(float(self.settle_every.get() or 10)),
                "ev_max": int(float(self.ev_max.get() or 12)),
                "material": int(float(self.material.get() or 8)),
                "attempts": int(float(self.attempts.get() or 3)),
                "style": self.style.get(),
                "quote_mode": self.quote_mode.get(),
                "cast_enable": bool(self.cast_enable.get()),
                "cast_n": int(float(self.cast_n.get() or 6)),
                "cast_hz": int(float(self.cast_hz.get() or 50)),
                "narrator": self.narrator.get().strip(),
                "out_dir": self.out_dir.get().strip(),
                "rewrite": bool(self.rewrite.get()),
            }
        except ValueError as e:
            raise ValueError(f"参数必须是数字：{e}")
        if c["card_lo"] >= c["card_hi"]:
            raise ValueError("普通卡：下限必须小于上限")
        if c["base_lo"] >= c["base_hi"]:
            raise ValueError("结算卡：下限必须小于上限")
        if not c["api_url"].startswith("http"):
            raise ValueError("API 地址要以 http:// 或 https:// 开头")
        if not c["model"]:
            raise ValueError("模型名不能为空")
        if not (10 <= c["cast_hz"] <= 80):
            raise ValueError("人物简介每人字数要在 10–80 之间")
        if not (1 <= c["cast_n"] <= 50):
            raise ValueError("每卡人物数要在 1–50 之间")
        return c

    def save_all(self):
        try:
            c = self.collect()
        except ValueError as e:
            messagebox.showerror("参数错误", str(e))
            return
        save_cfg(c)
        self.log("配置已保存到 long_summary_config.json")

    # ============================== API ==============================
    def test_api(self):
        if requests is None:
            messagebox.showerror("缺少依赖", "没有安装 requests：请在 .venv 里 pip install requests")
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
                r = requests.get(base + "/models", headers=h, timeout=15)
                d = r.json()
                items = d.get("data") or d.get("models") or []
                names = [(m.get("id") or m.get("name")) for m in items if isinstance(m, dict)]
                names = [n for n in names if n]
                self.ui(self._test_done, names, None)
            except Exception as e:
                self.ui(self._test_done, [], f"{type(e).__name__}: {e}")
        threading.Thread(target=work, daemon=True).start()

    def _test_done(self, names, err):
        self.btn_test.config(state="normal")
        if err:
            self.log("连接失败：" + err)
            messagebox.showerror("连接失败", err)
            return
        self.log("连接成功，端点模型：" + ("、".join(names[:5]) if names else "（空）"))
        if names and self.model.get().strip() not in names:
            self.model.set(names[0])
            self.log("已自动填入模型名：" + names[0])

    # ============================== 运行控制 ==============================
    def start(self):
        if self.running:
            return
        if requests is None:
            messagebox.showerror("缺少依赖", "没有安装 requests：请在 .venv 里 pip install requests")
            return
        try:
            c = self.collect()
        except ValueError as e:
            messagebox.showerror("参数错误", str(e))
            return
        src = self.src_path.get().strip()
        if not src or not os.path.exists(src):
            messagebox.showerror("缺少素材", "请先选择小说 txt 或章节目录")
            return
        if not c["out_dir"]:
            messagebox.showerror("缺少输出", "请先选择输出目录")
            return
        save_cfg(c)
        self.stop_event.clear()
        self.run_event.set()
        self.running = True
        self.paused = False
        self.api_calls = 0
        self.t_start = time.time()
        self.btn_start.config(state="disabled")
        self.btn_pause.config(state="normal", text="⏸ 暂停")
        self.btn_stop.config(state="normal")
        self.state_text.set("运行中")
        self.log("=" * 46)
        self.log(f"开始：{os.path.basename(src)} → {c['out_dir']}")
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
        self.run_event.set()      # 解除暂停，让它尽快走到检查点
        self.state_text.set("正在停止…")
        self.log("⏹ 收到停止请求，当前章节结束后停下")

    def _gate(self):
        """在每一步前调用：处理暂停与停止。返回 False 表示要退出。"""
        while not self.run_event.is_set():
            if self.stop_event.is_set():
                return False
            time.sleep(0.15)
        return not self.stop_event.is_set()

    def _finish(self, ok=True, msg=""):
        self.running = False
        self.paused = False
        self.btn_start.config(state="normal")
        self.btn_pause.config(state="disabled", text="⏸ 暂停")
        self.btn_stop.config(state="disabled")
        self.state_text.set("已完成" if ok else "已停止")
        if msg:
            self.log(msg)

    # ============================== 主流程 ==============================
    def _call(self, c, msgs, max_tokens):
        h = {"Content-Type": "application/json"}
        if c["api_key"]:
            h["Authorization"] = "Bearer " + c["api_key"]
        body = {"model": c["model"], "temperature": c["temp"],
                "max_tokens": max_tokens, "messages": msgs,
                # 关思考：本地量化模型常默认开思考，会把输出预算吃光导致 content 为空
                "chat_template_kwargs": {"enable_thinking": False},
                "reasoning_effort": "none"}
        r = requests.post(c["api_url"], json=body, headers=h, timeout=c["timeout"])
        r.raise_for_status()
        d = r.json()
        self.api_calls += 1
        msg = ((d.get("choices") or [{}])[0].get("message") or {})
        content = (msg.get("content") or "").strip()
        if not content:
            rc = msg.get("reasoning_content") or ""
            if rc:
                raise RuntimeError("content 为空，内容全在 reasoning 里（思考没关掉）")
            raise RuntimeError("空回复")
        return content

    @staticmethod
    def _decode(raw):
        """txt 常见三种编码：UTF-8（带不带 BOM）、GB18030/GBK、UTF-16。别直接判空。"""
        for enc in ("utf-8-sig", "utf-8", "gb18030", "utf-16"):
            try:
                t = raw.decode(enc)
            except (UnicodeDecodeError, UnicodeError):
                continue
            # gb18030 几乎什么都能"解"出来，用生僻字比例反查误判
            if enc == "gb18030" and sum(1 for ch in t[:5000] if ch in "锟斤拷") > 20:
                continue
            return t
        return raw.decode("utf-8", "ignore")

    def _read(self, p):
        try:
            with open(p, "rb") as f:
                return self._decode(f.read())
        except Exception:
            return ""

    def _load_chapters(self, src):
        """目录 → 逐文件；txt → 按「第X章」切；没有章标题就当整本一章（用文件名当标题）"""
        chs = []
        if os.path.isdir(src):
            for f in sorted(os.listdir(src)):
                if not f.lower().endswith(".txt"):
                    continue
                p = os.path.join(src, f)
                body = self._read(p)
                if not body.strip():
                    continue
                chs.append({"name": os.path.splitext(f)[0],
                            "title": body.split("\n", 1)[0].strip() or os.path.splitext(f)[0],
                            "text": body})
            return chs
        body = self._read(src).replace("\r\n", "\n")
        stem = os.path.splitext(os.path.basename(src))[0] or "book"
        cur, name = [], None

        def push():
            if not cur:
                return
            nm = name or (f"{stem}_开篇" if not chs else f"{stem}_{len(chs) + 1:04d}")
            chs.append({"name": nm, "title": (name or nm).strip(),
                        "text": "\n".join(cur)})

        for ln in body.split("\n"):
            if CH_HEAD.match(ln) and len(ln.strip()) <= 60:
                push()
                name, cur = ln.strip(), [ln]
            else:
                cur.append(ln)
        push()
        return chs

    def _pick_material(self, text, k):
        """按位置分箱取素材句：滤掉章标题／跨行块／残句，保证细节覆盖全章后段。"""
        n = len(text) or 1
        cand = []
        for m in re.finditer(r"[^。！？…\n]*[。！？…]", text):
            s = m.group(0).strip()
            if not (14 <= len(s) <= 60) or "\n" in s or CH_HEAD.match(s):
                continue
            if s.startswith(("”", "」", "’")):                  # 断在引号后的残句
                continue
            if s.count("“") != s.count("”") or s.count("「") != s.count("」"):
                continue
            if m.start() < n * 0.02:                           # 章首标题区
                continue
            score = 2 * len(QUOTED.findall(s))
            score += 1 if re.search(r"[眼手足唇发颤喘笑皱眉咬臂腰腿]", s) else 0
            cand.append((m.start(), score, s))
        per = max(1, k // 4)
        out = []
        for b in range(4):                                     # 前 1/4 到后 1/4 各取几条
            lo, hi = n * b / 4.0, n * (b + 1) / 4.0
            out += sorted([c for c in cand if lo <= c[0] < hi], key=lambda x: -x[1])[:per]
        out.sort(key=lambda x: x[0])
        return [(round(p * 100 / n), s) for p, _, s in out[:k]]

    @staticmethod
    def _parse_events(txt):
        rows, bad = [], 0
        for ln in (txt or "").split("\n"):
            if not ln.strip():
                continue
            m = EV_LINE.match(ln)
            if m:
                rows.append({"idx": int(m.group(1)), "ctx": m.group(2),
                             "desc": m.group(3).strip(), "w": float(m.group(4))})
            else:
                bad += 1
        return rows, bad

    # ---------------------- 叙述者：全书只判一次 ----------------------
    def _narr_path(self, task):
        return os.path.join(task, "叙述者.json")

    def _load_narr(self, task):
        try:
            with open(self._narr_path(task), encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}

    def _save_narr(self, task, d):
        try:
            with open(self._narr_path(task), "w", encoding="utf-8") as f:
                json.dump(d, f, ensure_ascii=False, indent=2)
        except Exception as e:
            self.ui(self.log, f"  叙述者.json 写失败：{e}")

    def _identify_narrator(self, c, task, chs, manual=""):
        """判定「我」是谁。manual 有值就直接用；否则只在全书开头问一次模型并落盘。"""
        d = self._load_narr(task)
        manual = (manual or "").strip()
        if manual:
            if d.get("name") != manual or d.get("source") != "manual":
                d = {"mode": "first", "name": manual, "source": "manual"}
                self._save_narr(task, d)
            return d
        if d.get("name") or d.get("mode"):
            return d
        head = (chs[0]["text"] if chs else "")[:2500]
        pov = detect_pov(head)
        if pov["verdict"] == "third":
            d = {"mode": "third", "name": "", "source": "auto"}
            self._save_narr(task, d)
            return d
        cands = [n for n, k in guess_narrator(head) if k >= 3][:6]
        user = f"【开头正文】\n{head}"
        if cands:
            user += f"\n\n【与「我」同段出现最多的人名（仅供参考，可能不对）】\n{'、'.join(cands)}"
        name, ev = "", ""
        for _ in range(max(1, min(2, int(c.get("attempts", 3))))):
            if not self._gate():
                break
            try:
                t = self._call(c, [{"role": "system", "content": SYS_NARR},
                                   {"role": "user", "content": user}], 160)
                self.ui(self.log, "  " + " / ".join(
                    x.strip() for x in (t or "").split("\n") if x.strip())[:80])
            except Exception as e:
                self.ui(self.log, f"  叙述者识别失败：{type(e).__name__}: {e}")
                time.sleep(1.5)
                continue
            mm = re.search(r"人称\s*[:：]\s*([^\n]+)", t or "")
            mn = re.search(r"叙述者\s*[:：]\s*([^\n]{1,12})", t or "")
            me_ = re.search(r"证据\s*[:：]\s*([^\n]+)", t or "")
            if mm and "第三" in mm.group(1) and "第一" not in mm.group(1):
                d = {"mode": "third", "name": "", "source": "auto"}
                self._save_narr(task, d)
                return d
            if mn:
                nm = re.sub(r"[「」『』“”\"'，。；：、\s]", "", mn.group(1))
                nm = re.sub(r"^(是|叫|名为|本名)", "", nm)
                if nm in NARR_WORDS or nm in ("无名", "未知", "不明"):
                    nm = ""
                if nm and 1 < len(nm) <= 4 and cjk_only(nm):
                    name, ev = nm, (me_.group(1) if me_ else "")
                break
        if name and name not in cjk_only(head):
            self.ui(self.log, f"  叙述者「{name}」在开头没出现，改用占位名")
            name = ""
        if not name:
            name = "主角"
            self.ui(self.log, "  ⚠ 原文没给叙述者名字/称呼，暂用「主角」；"
                              "界面「叙述者」填对后重跑，卡片会用这个名字")
        d = {"mode": "first", "name": name, "evidence": ev, "source": "auto"}
        self._save_narr(task, d)
        return d

    def _check_events(self, txt, book_cjk, ev_max, narrator=""):
        rows, bad = self._parse_events(txt)
        hard, soft = [], []
        # 「我」不是人名：人物栏里的代词换成叙述者，描述里的「我」也换成名字（台词不动）
        me_left = 0
        for r in rows:
            m = re.search(r"人物\s*[:：]\s*([^|｜)）]+)", r["ctx"])
            if m:
                toks = [p.strip() for p in re.split(r"[,，、;；/\s]+", m.group(1)) if p.strip()]
                new = []
                for p in toks:
                    if p in NARR_WORDS:
                        if not narrator:
                            me_left += 1
                            continue
                        p = narrator
                    if p and p not in new:
                        new.append(p)
                if new != toks:
                    r["ctx"] = r["ctx"][:m.start(1)] + ",".join(new) + r["ctx"][m.end(1):]
            if narrator:
                r["desc"] = map_me(r["desc"], narrator)
        if me_left:
            hard.append("「我」被当成人名（第一人称要用叙述者的名字）")

        if bad >= 3:
            hard.append(f"{bad} 行格式不合格")
        elif bad:
            soft.append(f"{bad} 行格式不合格（已丢弃）")
        if len(rows) < 6:
            hard.append(f"只解析出 {len(rows)} 条事件")
        elif len(rows) > ev_max + 8:
            soft.append(f"事件 {len(rows)} 条（上限 {ev_max}）")
        fake = []
        for r in rows:
            fields = {}
            for part in re.split(r"[|｜]", r["ctx"]):
                for sep in (":", "："):
                    if sep in part:
                        k, v = part.split(sep, 1)
                        fields[k.strip()] = v.strip()
                        break
            for name in re.split(r"[,，、;；/\s]+", fields.get("人物", "")):
                nm = (name or "").strip()
                if not looks_like_name(nm) or not cjk_only(nm) or cjk_only(nm) in book_cjk:
                    continue
                # 「裴母／裴父／长孙氏」这类是缩写称呼，不是编造的人名 → 只提示，不判死
                if nm[-1] in ROLE_TAIL or len(nm) <= 4 and re.search(r"[家氏]", nm):
                    soft.append(f"缩写称呼：{nm}")
                    continue
                fake.append(nm)
        if fake:
            hard.append("全书找不到名字：" + "、".join(sorted(set(fake))[:3]))
        return rows, hard, soft

    def _check_prose(self, txt, material, c, chapter_text="", offnames=(),
                     prev_names=(), must=(), rel_map=None, rel_trip=None, narrator=""):
        hard, soft = [], []
        hz = n_hz(txt)
        if not (c["card_lo"] <= hz <= c["card_hi"]):
            soft.append(f"{hz} 字（要求 {c['card_lo']}–{c['card_hi']}）")
        # 统一第三人称：正文里不该出现叙述用的「我」（引号台词里的我照旧放行）
        if narrator:
            me = count_me(txt)
            if me:
                soft.append(f"正文出现「我」{me} 处（应写叙述者 {narrator}）")
        used = QUOTED.findall(txt)
        # 引文只在「原文全章」里核验：模型引的真句子不必来自素材句，但绝不能无中生有
        src = cjk_only(chapter_text) if chapter_text else cjk_only("".join(q for _, q in material))
        bad = [q for q in used if len(cjk_only(q)) >= MIN_QUOTE_CJK and cjk_only(q) not in src]
        if bad:
            hard.append("引文原文里没有（疑似自造台词）：" + "、".join(f"「{q[:12]}」" for q in bad[:2]))
        qmax = QUOTE_MAX.get(c.get("quote_mode", "转述"), 0)
        if qmax == 0 and used:
            soft.append(f"引语 {len(used)} 处（转述模式应无引号台词）")
        elif qmax and len(used) > qmax:
            soft.append(f"原样引语 {len(used)} 处（上限 {qmax}，其余应转述）")
        if re.match(r"^第[0-9零一二三四五六七八九十百]+章", txt.strip()):
            hard.append("开头带了章标题")
        if re.search(r"与此同时|就在这时，另一边|而在另一边", txt):
            soft.append("用了硬切过渡")
        off = [n for n in (offnames or ()) if n and n in txt]
        if off:
            soft.append("疑似串人（本章事件行没有）：" + "、".join(off[:3]))
        # 承接：开头两句该点到上一章延续下来的人
        if prev_names:
            head = txt[:130]
            if not any(n in head for n in prev_names):
                soft.append("开头没接上一张卡（前两句没点到上一章的人）")
        # 覆盖：高权重事件里一个人都没在正文出现 = 漏写
        missed = [lab for lab, names in (must or ())
                  if names and not any(n in txt for n in names)]
        if missed:
            soft.append("漏写重要事件：" + "、".join(missed[:2]))
        # 称谓一致性：正文给某人安的亲缘词，必须和已确认人物关系一致
        if rel_map:
            for nm, cl in rel_claims(txt, list(rel_map)).items():
                bad = rel_conflict(rel_map.get(nm) or set(), cl)
                if bad:
                    soft.append(f"称谓与前文冲突：{nm}（{'、'.join(bad)}）")
        # 带持有者的亲缘：X的(妻子/女儿…) 与前文不符也算错（覆盖继母写成女儿这类）
        if rel_trip:
            names = {k.split("|")[0] for k in rel_trip} | {k.split("|")[1] for k in rel_trip}
            for (holder, subj), rels in rel_triples(txt, list(names)).items():
                o = set(rel_trip.get(f"{holder}|{subj}") or ())
                if o and rels and not (rels & o):
                    soft.append(f"称谓与前文冲突：{holder}的{'/'.join(sorted(rels))}"
                                f"（前文 {subj} 是{holder}的{'/'.join(sorted(o))}）")
        return hard, soft, hz, len(used)

    # ---------------------------- 场景 / 台账 ----------------------------
    @staticmethod
    def _clamp_rows(rows, ev_max):
        """短文只吃权重前 ev_max 条（按时序保留），其余由程序折算成一句交代。"""
        if len(rows) <= ev_max:
            return rows, 0
        keep = sorted(rows, key=lambda r: -r["w"])[:ev_max]
        kept_ids = {id(r) for r in keep}
        kept = [r for r in rows if id(r) in kept_ids]
        return kept, len(rows) - len(kept)

    @staticmethod
    def _cjk_prefix_pos(s, k):
        """s 里前 k 个汉字结束处的下标。"""
        n = 0
        for i, ch in enumerate(s):
            if CJK.match(ch):
                n += 1
                if n == k:
                    return i + 1
        return None

    def _repair_quotes(self, txt, chapter_text):
        """把引号里被续写/改字的台词收回到原文：先截到真实前缀，再找最像的原文引语。"""
        ch = cjk_only(chapter_text)
        real = QUOTED.findall(chapter_text)
        fixed = 0
        for q in set(QUOTED.findall(txt)):
            cq = cjk_only(q)
            if len(cq) < MIN_QUOTE_CJK or cq in ch:
                continue
            new = ""
            for k in range(len(cq) - 1, MIN_QUOTE_CJK - 1, -1):       # 真句子被续写：留真实前缀
                if cq[:k] in ch:
                    pos = self._cjk_prefix_pos(q, k)
                    if pos:
                        new = q[:pos].rstrip("，、,；;：: ")
                    break
            if not new and real:                       # 改过字：找最接近的原文引语
                best = max(real, key=lambda r: SequenceMatcher(None, cq, cjk_only(r)).ratio())
                if SequenceMatcher(None, cq, cjk_only(best)).ratio() >= 0.45:
                    new = best
            if not new or new == q:
                continue
            for a, b in (("「" + q + "」", "「" + new + "」"),
                         ("“" + q + "”", "“" + new + "”")):
                if a in txt:
                    txt = txt.replace(a, b)
                    fixed += 1
        return txt, fixed

    @staticmethod
    def _group_scenes(rows, maxn=6):
        """把扁平事件行按地点聚成 3–6 个场面：清单式输入只会换回清单式输出。"""
        if not rows:
            return ""

        def field(r, key):
            m = re.search(key + r"\s*[:：]\s*([^|｜)）]+)", r["ctx"])
            return m.group(1).strip() if m else ""

        groups = []
        for r in rows:
            loc = field(r, "地点") or "未明"
            if groups and groups[-1]["loc"] == loc:
                groups[-1]["rows"].append(r)
            else:
                groups.append({"loc": loc, "rows": [r]})
        while len(groups) > maxn:
            i = min(range(len(groups) - 1),
                    key=lambda j: len(groups[j]["rows"]) + len(groups[j + 1]["rows"]))
            if groups[i]["loc"] != groups[i + 1]["loc"]:
                groups[i]["loc"] += " / " + groups[i + 1]["loc"]
            groups[i]["rows"] += groups[i + 1]["rows"]
            del groups[i + 1]

        out = []
        for gi, g in enumerate(groups, 1):
            rs = g["rows"]
            people = []
            for r in rs:
                for p in re.split(r"[,，、;；/\s]+", field(r, "人物")):
                    if p and p not in people:
                        people.append(p)
            t0, t1 = field(rs[0], "时间"), field(rs[-1], "时间")
            tspan = t0 if (not t1 or t1 == t0) else f"{t0} → {t1}"
            out.append(f"【场景{gi}】地点：{g['loc']}｜时间：{tspan or '未明'}"
                       f"｜人物：{'、'.join(people[:8]) or '未明'}")
            out += [f"  - {r['desc']}（重要度 {r['w']}）" for r in rs]
        return "\n".join(out)

    @staticmethod
    def _parse_ledger(raw):
        """8 列（带锚点）/ 7 列 / 旧版 6 列台账都能读；分类一律归一。"""
        rows = []
        for ln in (raw or "").split("\n"):
            ln = ln.strip().strip("\ufeff").strip("`")
            if "\t" not in ln:
                continue
            f = [x.strip() for x in ln.split("\t")]
            anch = ""
            if len(f) >= 8:
                cat, name, alias, role, loc, note, wraw = f[:7]
                anch = f[7]
            elif len(f) == 7:
                cat, name, alias, role, loc, note, wraw = f
            elif len(f) == 6:
                cat, name, role, loc, note, wraw = f
                alias = ""
            else:
                continue
            cat = norm_cat(cat)
            if not cat or not name:
                continue
            try:
                w = float(re.sub(r"[^\d.]", "", wraw) or 0)
            except Exception:
                w = 0.0
            rows.append({"cat": cat, "name": name, "alias": alias, "role": role,
                         "loc": loc, "note": note, "w": max(0.0, min(1.0, w)),
                         "anch": anch})
        return rows

    @staticmethod
    def merge_ledger(ledger, rows, no):
        """按 (分类, 名称) 增量合并：首末章、出现章数（按章去重）、别名、身份（取最醒目章）。"""
        for r in rows:
            key = (r["cat"], r["name"])
            al = [x.strip() for x in re.split(r"[,，、/]+", r.get("alias") or "") if x.strip()]
            cur = ledger.get(key)
            if cur:
                cur["chs"].add(no)
                cur["n"] = len(cur["chs"])
                cur["last"] = max(cur["last"], no)
                cur["w"] = max(cur["w"], r["w"])
                cur.setdefault("aliases", set()).update(al)
                # 身份取「当事人最醒目那一章」的写法，避免路人甲的标签串到主角身上
                if r["role"] and r["w"] >= cur.get("role_w", -1):
                    cur["role"], cur["role_w"] = r["role"], r["w"]
                if r["note"]:
                    cur["note"], cur["note_ch"] = r["note"], no
                    cur["anch"] = r.get("anch") or cur.get("anch", "")
            else:
                ledger[key] = {"cat": r["cat"], "name": r["name"], "role": r["role"],
                               "role_w": r["w"] if r["role"] else -1,
                               "aliases": set(al), "note": r["note"],
                               "first": no, "last": no, "note_ch": no,
                               "anch": r.get("anch", ""),
                               "n": 1, "w": r["w"], "chs": {no}}

    @staticmethod
    def _dedupe(rows):
        """同一章里同一名称出现多行 → 合成一行（要点取长的，权重取高的）。"""
        out, idx = [], {}
        for r in rows:
            k = (r["cat"], r["name"])
            if k in idx:
                cur = idx[k]
                if len(r["note"]) > len(cur["note"]):
                    cur["note"] = r["note"]
                if r["role"] and not cur["role"]:
                    cur["role"] = r["role"]
                cur["w"] = max(cur["w"], r["w"])
                continue
            r = dict(r)
            idx[k] = r
            out.append(r)
        return out

    @staticmethod
    def _anchor(text, name):
        """回本章原文取含该名称的第一句前 24 字当锚点（供事后 grep 核验，可追溯）。"""
        if not text or not name:
            return ""
        for sent in re.split(r"(?<=[。！？；\n])", text):
            if name in sent:
                return sent.strip().replace("\n", "")[:24]
        return ""

    def _clean_ledger_rows(self, rows, ch, ev, ledger, dropped, no):
        """闸门：分类归一 → 人物章必须是真的人 → 别名回填正名 → 补原文锚点。
        丢掉的行走 dropped（落 _dropped.tsv，不静默）。"""
        ev_names = set()
        for r in self._parse_events(ev)[0]:
            m = re.search(r"人物\s*[:：]\s*([^|｜)）]+)", r["ctx"])
            if m:
                ev_names.update(p.strip() for p in
                                re.split(r"[,，、;；/\s]+", m.group(1)) if p.strip())
        alias2name, lnames = {}, set()
        for v in ledger.values():
            if v["cat"] != "人物章":
                continue
            lnames.add(v["name"])
            for a in v.get("aliases") or ():
                if a and a != v["name"]:
                    alias2name[a] = v["name"]
        text = ch.get("text") or ""
        out = []
        for r in rows:
            r = dict(r)
            nm = r["name"]
            if nm in alias2name:                        # 别名 → 正名（回填）
                real = alias2name[nm]
                al = r.get("alias") or ""
                if nm not in al:
                    r["alias"] = (al + "," + nm).strip(",") if al else nm
                r["name"] = real
            if r["cat"] == "人物章" and not person_ok(r["name"], ev_names, lnames):
                dropped.append((no, r["cat"], r["name"], "人物章但不是人名（器物/地名/泛称）"))
                continue
            r["note"] = re.sub(r"\s+", " ", r.get("note") or "").strip()
            if r["note"] in ("", "无", "无变化", "-", "→"):
                r["note"] = ""
            if not r.get("anch"):
                r["anch"] = self._anchor(text, r["name"])
            out.append(r)
        return out

    def _fill_ledger(self, c, no, ch, ev, ledger, ledger_dir):
        """填本章台账：调用 → 闸门清洗 → 落盘 8 列。已填过只清洗，续跑不重复花调用。"""
        p = os.path.join(ledger_dir, f"ch_{no:04d}.tsv")
        raw = self._read(p)
        dropped, rows = [], []
        if raw.strip():
            rows = self._clean_ledger_rows(self._dedupe(self._parse_ledger(raw)),
                                           ch, ev, ledger, dropped, no)
        for a in range(0 if rows else min(2, max(1, c["attempts"]))):
            if not self._gate():
                break
            fb = ""
            if dropped:
                bad = "；".join(f"{x[2]}（{x[3]}）" for x in dropped[:8])
                fb = ("\n\n上一版这些行不合格已被丢弃：" + bad +
                      "。重填时：没有名字的泛称、物品、地点、功法、身体部位一律不进人物章；"
                      "分类只能写 人物章/势力/地点/物品/设定。")
            try:
                t = self._call(c, [{"role": "system", "content": SYS_TABLE},
                                   {"role": "user", "content":
                                    f"【本章】{ch['title']}\n【事件行】\n{ev}{fb}"}], 1800)
            except Exception as e:
                self.ui(self.log, f"  台账请求失败：{type(e).__name__}: {e}")
                time.sleep(2)
                continue
            parsed = self._dedupe(self._parse_ledger(t))
            drop2 = []
            got = self._clean_ledger_rows(parsed, ch, ev, ledger, drop2, no)
            self.ui(self.log, f"  台账 试{a+1}: {len(got)} 行"
                              + (f"，弃 {len(drop2)} 行" if drop2 else " ✓"))
            if not got:
                continue
            if not rows or len(got) >= len(rows):
                rows, dropped = got, drop2
            if not drop2 or len(drop2) <= 0.3 * max(len(parsed), 1):
                break
        if dropped:
            with open(os.path.join(ledger_dir, "_dropped.tsv"), "a", encoding="utf-8") as f:
                for x in dropped:
                    f.write("\t".join(str(y) for y in x) + "\n")
        if rows:
            lines = ["\t".join([r["cat"], r["name"], r.get("alias") or "", r.get("role") or "",
                                r.get("loc") or "", r.get("note") or "", f"{r['w']:.2f}",
                                r.get("anch") or ""]) for r in rows]
            open(p, "w", encoding="utf-8").write("\n".join(lines) + "\n")
        self.merge_ledger(ledger, rows, no)
        return rows

    def _ledger_context(self, ledger, rows, limit=1400):
        """本章点到的人/地点 → 台账摘要（含别名），给短文当背景。"""
        if not ledger:
            return ""
        names, places = set(), set()
        for r in rows:
            m = re.search(r"人物\s*[:：]\s*([^|｜)）]+)", r["ctx"])
            if m:
                names.update(p.strip() for p in re.split(r"[,，、;；/\s]+", m.group(1)) if p.strip())
            m = re.search(r"地点\s*[:：]\s*([^|｜)）]+)", r["ctx"])
            if m:
                places.add(m.group(1).strip())
        alias2name = {}
        for v in ledger.values():
            for a in v.get("aliases") or ():
                if a != v["name"]:
                    alias2name[a] = v["name"]
        hit = {alias2name.get(n, n) for n in names}
        out = []
        for v in ledger.values():
            if v["cat"] == "人物章":
                if v["name"] not in hit:
                    continue
                al = "、".join(sorted(x for x in (v.get("aliases") or ()) if x != v["name"]))
                head = v["name"] + (f"（别名 {al}）" if al else "")
                bits = [x for x in (v["role"], v["note"]) if x]
                if bits:
                    out.append("人物｜" + head + "｜" + "｜".join(bits))
            else:
                if not any(v["name"] in p for p in places):
                    continue
                if v.get("note"):
                    out.append(f"{v['cat']}｜{v['name']}｜{v['note']}")
        return "\n".join(out)[:limit]

    # ---------------------------- 本章重要人物简介 ----------------------------
    @staticmethod
    def _cast_people(rows, ledger):
        """本章事件行点到的人名 + 台账里的人物名（用来挡编造出来的名字）。"""
        ev_names, led_names = set(), set()
        for r in rows or ():
            m = re.search(r"人物\s*[:：]\s*([^|｜)）]+)", r.get("ctx", ""))
            if m:
                ev_names.update(p.strip() for p in re.split(r"[,，、;；/\s]+", m.group(1)) if p.strip())
        for v in (ledger or {}).values():
            if v.get("cat") == "人物章":
                led_names.add(v["name"])
        return ev_names, led_names

    def _make_cast(self, c, title, ledger, rows, prev_cast="", ch_text="", narrator=""):
        """一章的「重要人物简介」：一人一句，≤cast_hz 汉字，必须带社会关系。"""
        if not c.get("cast_enable", True) or not rows:
            return []
        hz = int(c.get("cast_hz", 50))
        maxn = int(c.get("cast_n", 6))
        ev_names, led_names = self._cast_people(rows, ledger)
        # 人名候选：事件行点到的 + 台账里、本章原文确实出现的（防止漏掉没写进事件行的配角）
        cand = [n for n in sorted(ev_names) if is_person_name(n) or n == narrator]
        if ch_text:
            ct = cjk_only(ch_text)
            extra = [v["name"] for v in (ledger or {}).values()
                     if v.get("cat") == "人物章" and len(v["name"]) >= 2
                     and v["name"] in ct and v["name"] not in cand
                     and is_person_name(v["name"])]
            cand += extra
        if narrator and narrator not in cand:
            cand.insert(0, narrator)
        evs = "\n".join(f"{r['idx']}: {r['desc']}（权重 {r['w']:.2f}）"
                        for r in rows[:max(60, 3 * maxn)])
        user = f"【本章】{title}\n\n【事件行（权重）】\n{evs}"
        if narrator:
            user += (f"\n\n【叙述者】本章是第一人称叙述，原文的「我」＝{narrator}。"
                     f"{narrator} 是本书叙述者，必须排在人物表第一行，"
                     f"身份里写明「本书叙述者」。")
        if cand:
            user += f"\n\n【人名候选（本章出场的有名字的人，逐个都要写一行）】\n{'、'.join(cand[:60])}"
            ev_txt = relation_evidence(cand[:20], ch_text)
            if ev_txt:
                user += f"\n\n【原文证据（人名＋亲缘原句；定身份以它为准）】\n{ev_txt}"
        led = self._ledger_context(ledger, rows, limit=max(900, 120 * maxn))
        if led:
            user += f"\n\n【台账：身份／状态】\n{led}"
        if prev_cast:
            user += ("\n\n【上一张卡的人物简介（称谓与关系照它保持一致；"
                     "本章没出场的人不要写）】\n" + prev_cast[:max(800, 60 * maxn)])
        sysc = SYS_CAST.format(hz=hz, n=maxn)
        for _ in range(max(1, min(3, int(c.get("attempts", 3))))):
            if not self._gate():
                return []
            try:
                t = self._call(c, [{"role": "system", "content": sysc},
                                   {"role": "user", "content": user}],
                               200 + 110 * maxn)
            except Exception as e:
                self.ui(self.log, f"  人物简介请求失败：{type(e).__name__}: {e}")
                time.sleep(1.5)
                continue
            rr = [(n, d) for n, d in parse_cast(t, hz, maxn)
                  if is_person_name(n) or n == narrator]
            if rr:
                return rr[:maxn]
        return []

    @staticmethod
    def append_cast(path, rows):
        """把人物简介块追加到卡片/结算卡末尾。"""
        blk = cast_block(rows)
        if not blk:
            return False
        with open(path, "a", encoding="utf-8") as f:
            f.write("\n\n" + blk + "\n")
        return True

    # ---------------------------- 人物关系册（跨章一致性） ----------------------------
    def _rel_path(self, task):
        return os.path.join(task, "人物关系.json")

    def _load_rel(self, task):
        """已确认的人物关系：{名: {text, ch, claims}}。跨章沿用，断点续跑也在。"""
        p = self._rel_path(task)
        if os.path.exists(p):
            try:
                return json.load(open(p, encoding="utf-8")) or {}
            except Exception:
                pass
        return {}

    def _save_rel(self, task, rel):
        try:
            json.dump(rel, open(self._rel_path(task), "w", encoding="utf-8"),
                      ensure_ascii=False, indent=1)
        except Exception:
            pass

    def _fix_identity(self, id_rows, rel, ch_text, no):
        """本章身份 vs 人物关系册：冲突就回原文数证据，证据不足则沿用前文。

        两道关：① 性别互斥词（儿子/女儿…）② 带持有者的亲缘（谁的妻子/女儿）。
        返回 (修正后的 id_rows, 关系册, 说明列表)。
        """
        notes, out = [], []
        rows = [(n, t) for n, t in (id_rows or ())]
        for idx, (name, text) in enumerate(rows):
            new_claims = declared_rels([(name, text)]).get(name) or set()
            old = rel.get(name) or {}
            old_claims = set(old.get("claims") or ())
            bad = rel_conflict(old_claims, new_claims)
            if old and bad:
                sup_new = sum(rel_support(name, [w for w in new_claims], ch_text).values())
                sup_old = sum(rel_support(name, [w for w in old_claims], ch_text).values())
                if sup_new > sup_old:          # 原文支持更正（情节真变了/前面写错了）
                    notes.append(f"{name}：{'、'.join(bad)} → 原文证据支持本章写法，已更正")
                else:                          # 没证据或证据偏向前文 → 沿用前文
                    text = self._rewrite_head(text, old_claims, new_claims)
                    notes.append(f"{name}：{'、'.join(bad)} → 沿用前文"
                                 f"（本章原文证据 {sup_new} 条 / 前文 {sup_old} 条）")
                    new_claims = declared_rels([(name, text)]).get(name) or old_claims
            # ② 带持有者的亲缘：X的(妻子/女儿/母亲…) 不能有两个
            def _rows_with(cur_name=name, cur_text=text):
                return [(n2, cur_text if n2 == cur_name else t2) for n2, t2 in rows]

            old_t = dict(old.get("triples") or {})
            new_t = {k: v for k, v in id_triples(_rows_with()).items() if k[1] == name}
            for (holder, subj), rels in new_t.items():
                key = f"{holder}|{subj}"
                o = set(old_t.get(key) or ())
                if not o or not rels or (rels & o):
                    old_t[key] = sorted(set(o) | set(rels))
                    continue
                wn = sum(triple_support(holder, subj, w, ch_text) for w in rels)
                wo = sum(triple_support(holder, subj, w, ch_text) for w in o)
                if wn > wo:
                    old_t[key] = sorted(rels)
                    notes.append(f"{name}：{holder}的{'/'.join(sorted(rels))}"
                                 f"（前文为{'/'.join(sorted(o))}）→ 原文证据支持，已更正")
                else:
                    text = self._rewrite_head(text, o, rels)
                    rows[idx] = (name, text)
                    rr = id_triples(_rows_with()).get((holder, subj)) or set()
                    old_t[key] = sorted(rr | o)
                    notes.append(f"{name}：{holder}的{'/'.join(sorted(rels))}"
                                 f"（前文为{'/'.join(sorted(o))}）→ 沿用前文"
                                 f"（本章证据 {wn} 条 / 前文 {wo} 条）")
            merged = set(old_claims) | set(new_claims)
            rel[name] = {"text": text, "ch": no, "claims": sorted(merged), "triples": old_t}
            out.append((name, text))
        return out, rel, notes

    @staticmethod
    def _rewrite_head(text, keep_claims, drop_claims):
        """只改身份段：把错词换成前文的说法，动作句（分号之后）一个字不动。"""
        head, sep, tail = str(text).partition("；")
        for a, b in REL_PAIRS:
            if a in keep_claims and b in head:
                head = head.replace(b, a)
            if b in keep_claims and a in head:
                head = head.replace(a, b)
        for w in drop_claims:              # 非互斥对（如 妻子↔女儿）：直接把错词换回对的
            if w in head and w not in keep_claims and keep_claims:
                for good in keep_claims:
                    if good not in head:
                        head = head.replace(w, good)
                        break
        return head + (sep + tail if sep else "")

    @staticmethod
    def _store_identity(rel, id_rows, no):
        """把最终身份文本写回关系册（claims 取并集，triples 保留历史）。"""
        for n, t in id_rows or ():
            e = rel.get(n) or {"text": "", "ch": 0, "claims": [], "triples": {}}
            e["text"] = t
            e["ch"] = no
            cl = set(e.get("claims") or ())
            cl |= declared_rels([(n, t)]).get(n) or set()
            e["claims"] = sorted(cl)
            rel[n] = e
        return rel

    # ---------------------------- 身份体检 / 纠正（正文前必须过） ----------------------------
    def _audit_identity(self, id_rows, rel, ch_text, narrator=""):
        """身份体检：性别有没有、亲缘有没有、名字本章真出现吗、和关系册冲突吗。"""
        issues, ch = [], cjk_only(ch_text)
        for name, text in id_rows or ():
            head = re.split(r"[；;]", str(text or ""))[0]
            if not re.search(r"[男女]性|男性|女性|男|女|中性|无性别|未明", head):
                issues.append((name, "缺性别"))
            has_rel = (any(w in head for w in REL_ALL)
                       or re.search(r"[\u4e00-\u9fff]{2,4}[之的][\u4e00-\u9fff]{1,5}", head))
            if not has_rel:
                issues.append((name, "缺亲缘/身份"))
            if ch and name not in ch and name != narrator:
                issues.append((name, "本章原文没出现"))
            old = set((rel.get(name) or {}).get("claims") or ())
            bad = rel_conflict(old, declared_rels([(name, text)]).get(name) or set())
            if old and bad:
                issues.append((name, "与关系册冲突：" + "、".join(bad)))
        return issues

    def _repair_identity(self, id_rows, rel, ch_text, issues, narrator=""):
        """按体检结果纠正：缺性别/缺身份→从关系册补；本章没出现的→删掉；冲突→用关系册覆盖。"""
        drop_names = {n for n, why in issues
                      if why == "本章原文没出现" and n != narrator}
        out = []
        for name, text in id_rows or ():
            if name in drop_names:
                self.ui(self.log, f"  ⚖ 去掉「{name}」：本章原文里没出现")
                continue
            old = rel.get(name) or {}
            head, sep, tail = str(text).partition("；")
            fixed = head
            for w in ("缺性别", "缺亲缘/身份"):
                if not any(why == w for n, why in issues if n == name):
                    continue
                src = str(old.get("text") or "")
                if w == "缺性别" and not re.search(r"[男女]|中性|无性别", fixed):
                    g = re.search(r"([男女]性|男性|女性|中性|无性别)", src)
                    fixed = (g.group(1) + "、" + fixed) if g else ("性别未明、" + fixed)
                if w == "缺亲缘/身份" and not any(x in fixed for x in REL_ALL):
                    rel_bit = None
                    for key, rels in (old.get("triples") or {}).items():
                        h, _, sname = str(key).partition("|")
                        if sname == name and rels:
                            rel_bit = f"{h}的{rels[0]}"
                            break
                    if rel_bit:
                        fixed = fixed + "、" + rel_bit
                    else:
                        fixed = fixed + "、身份未明"
            if any(why.startswith("与关系册冲突") for n, why in issues if n == name):
                keep = set(old.get("claims") or ())
                fixed = self._rewrite_head(fixed, keep, set(REL_ALL))
            out.append((name, fixed + (sep + tail if sep else "")))
        return out


    # ---------------------------- 任务目录 / 汇总 ----------------------------
    def make_task_dir(self, out_dir, src):
        """输出放到 out 下的单独文件夹：任务时间_原文件夹名。已存在同源任务则复用最新的（续跑）。"""
        base = os.path.basename(str(src).rstrip("\\/"))
        if os.path.isfile(src):
            base = os.path.splitext(base)[0]
        base = re.sub(r'[\\/:*?"<>|]', "_", base) or "task"
        os.makedirs(out_dir, exist_ok=True)
        olds = [d for d in os.listdir(out_dir)
                if os.path.isdir(os.path.join(out_dir, d)) and d.endswith("_" + base)]
        if olds:
            olds.sort()
            return os.path.join(out_dir, olds[-1]), True
        ts = time.strftime("%Y%m%d_%H%M%S")
        p = os.path.join(out_dir, f"{ts}_{base}")
        os.makedirs(p, exist_ok=True)
        return p, False

    def build_ledger_md(self, task_dir, chs, stems=None):
        """人物 × 章节 台账：md 供人读，tsv/json 供程序秒查。"""
        ledger_dir = os.path.join(task_dir, "ledger")
        hist = {}
        if os.path.isdir(ledger_dir):
            for f in sorted(os.listdir(ledger_dir)):
                m = re.match(r"ch_(\d+)\.tsv$", f)
                if m:
                    rows = self._parse_ledger(self._read(os.path.join(ledger_dir, f)))
                    if rows:
                        hist[int(m.group(1))] = self._dedupe(rows)
        if not hist:
            return "", 0
        title_of = {i: (ch.get("title") or "").strip() for i, ch in enumerate(chs, 1)}
        persons, others, ch_loc, ch_ppl = {}, {}, {}, {}
        for no in sorted(hist):
            locs, ppl = [], []
            for r in hist[no]:
                if r["cat"] == "人物章":
                    p = persons.setdefault(r["name"], {"role": "", "role_w": -1,
                                                       "aliases": set(), "rows": []})
                    p["aliases"].update(x.strip() for x in
                                        re.split(r"[,，、/]+", r.get("alias") or "") if x.strip())
                    if r["role"] and r["w"] >= p["role_w"]:
                        p["role"], p["role_w"] = r["role"], r["w"]
                    p["rows"].append((no, r["note"], r["w"]))
                    ppl.append((r["w"], r["name"]))
                else:
                    o = others.setdefault((r["cat"], r["name"]),
                                          {"first": no, "last": no, "n": 0, "note": "", "w": 0.0})
                    o["n"] += 1
                    o["last"] = no
                    o["w"] = max(o["w"], r["w"])
                    if r["note"]:
                        o["note"] = r["note"]
                if r["loc"] and r["loc"] not in locs:
                    locs.append(r["loc"])
            ch_loc[no] = locs
            ppl.sort(reverse=True)
            ch_ppl[no] = [x[1] for x in ppl]

        def clean(s):
            return (s or "").replace("|", "／").replace("\n", " ").strip()

        mine = os.path.basename(task_dir).split("_", 2)[-1]
        lines = [f"# 全书台账｜{mine}", "",
                 f"- 覆盖 {len(hist)} 章｜人物 {len(persons)} 位｜专名 {len(others)} 条",
                 "- 坐标：人物 × 章节。查某人看「人物轴」，查某章看「章节轴」",
                 "- 机器可用：`台账_人物章节.tsv`（长表）、`台账_索引.json`（人物→章号→要点）",
                 "", "---", "", "## 人物轴", ""]
        for name, v in sorted(persons.items(), key=lambda kv: -len(kv[1]["rows"])):
            nos = [r[0] for r in v["rows"]]
            role = ("（" + clean(v["role"]) + "）") if v["role"] else ""
            al = "、".join(sorted(x for x in v["aliases"] if x and x != name))
            al = ("｜别名 " + clean(al)) if al else ""
            span = f"第 {min(nos)} 章" if min(nos) == max(nos) else f"第 {min(nos)}–{max(nos)} 章"
            lines.append(f"### {name}{role}{al}｜{span}｜出现 {len(nos)} 章")
            lines.append("")
            for no, note, _w in v["rows"]:
                lines.append(f"- 第{no:03d}章（{clean(title_of.get(no, ''))[:16]}）：{clean(note)}")
            lines.append("")
        # 身份共用提示：单数头衔（总裁/女仆长…）挂到两个人身上，基本就是串号
        TITLES = ("总裁", "女仆长", "主教", "统领", "国王", "王后", "公主", "将军", "会长",
                  "所长", "校长", "工头", "掌门", "宗主", "家主", "管家", "丈夫", "妻子",
                  "首领", "团长", "队长", "长老", "供奉", "祭司", "圣女", "执政", "老板")
        by_role = {}
        for name, v in persons.items():
            if v["role"]:
                by_role.setdefault(v["role"], []).append(name)
        dup = {k: v for k, v in by_role.items() if len(v) == 2}
        if dup:
            def is_conflict(role, names):
                return (names[0] in names[1] or names[1] in names[0]
                        or names[0] in role or names[1] in role
                        or role.endswith(TITLES))
            strong = {k: v for k, v in dup.items() if is_conflict(k, v)}
            weak = {k: v for k, v in dup.items() if k not in strong}
            if strong:
                lines += ["### ⚠ 身份冲突（单数头衔挂给两人／名字互相包含，基本是串号）", ""]
                for role, names in sorted(strong.items()):
                    lines.append(f"- 「{clean(role)}」：{' / '.join(names)}")
                lines.append("")
            if weak:
                lines += ["### 身份共用（可能正常，如同一组织/同一群体，供参考）", ""]
                for role, names in sorted(weak.items()):
                    lines.append(f"- 「{clean(role)}」：{' / '.join(names)}")
                lines.append("")
        lines += ["---", "", "## 章节轴", "",
                  "| 章 | 标题 | 地点 | 人物（按重要度） | 主线事件 |",
                  "|---|---|---|---|---|"]
        for no in sorted(hist):
            ep = os.path.join(task_dir, "cards",
                              (stems[no - 1] if stems and no - 1 < len(stems) else f"{no:04d}")
                              + ".events.md")
            if not os.path.exists(ep):
                ep = os.path.join(task_dir, "cards", f"{no:04d}.events.md")
            rows, _ = self._parse_events(self._read(ep))
            main = max(rows, key=lambda r: r["w"])["desc"] if rows else ""
            lines.append(f"| {no:03d} | {clean(title_of.get(no, ''))[:18]} | "
                         f"{clean('、'.join(ch_loc[no])[:24])} | "
                         f"{clean('、'.join(ch_ppl[no][:5]))} | {clean(main)[:40]} |")
        lines.append("")
        for cat in ("势力", "地点", "物品", "设定"):
            rows = [(k[1], v) for k, v in others.items() if k[0] == cat]
            if not rows:
                continue
            rows.sort(key=lambda x: (-x[1]["n"], -x[1]["w"]))
            lines += [f"## {cat}（{len(rows)}）", "",
                      "| 名称 | 首章 | 末章 | 出现 | 最新状态 | 重要度 |",
                      "|---|---|---|---|---|---|"]
            for name, v in rows:
                lines.append(f"| {clean(name)} | {v['first']:03d} | {v['last']:03d} | "
                             f"{v['n']} | {clean(v['note'])[:40]} | {v['w']:.2f} |")
            lines.append("")

        md_p = os.path.join(task_dir, "全书台账.md")
        open(md_p, "w", encoding="utf-8").write("\n".join(lines))

        tsv = ["人物\t章\t身份\t要点\t重要度"]
        for name, v in persons.items():
            for no, note, w in sorted(v["rows"]):
                tsv.append(f"{name}\t{no:04d}\t{clean(v['role'])}\t{clean(note)}\t{w:.2f}")
        open(os.path.join(task_dir, "台账_人物章节.tsv"), "w",
             encoding="utf-8").write("\n".join(tsv))

        index = {"任务": mine,
                 "人物": {name: {"身份": v["role"],
                                 "别名": sorted(x for x in v.get("aliases") or () if x != name),
                                 "章号": sorted(r[0] for r in v["rows"]),
                                 "要点": {str(r[0]): r[1] for r in sorted(v["rows"])}}
                          for name, v in persons.items()},
                 "章节": {str(no): {"标题": title_of.get(no, ""),
                                    "地点": ch_loc[no], "人物": ch_ppl[no]}
                          for no in sorted(hist)}}
        json.dump(index, open(os.path.join(task_dir, "台账_索引.json"), "w", encoding="utf-8"),
                  ensure_ascii=False, indent=1)
        return md_p, len(persons)

    def build_merged_md(self, task_dir, chs, c, warn, ledger=None, stems=None):
        """把所有单章短文按「文件名为标题 + 人物简介 + 正文」拼成一份汇总 md。"""
        cards_dir = os.path.join(task_dir, "cards")
        if not stems:
            stems = [safe_stem((ch.get("name") or ch.get("title") or f"{i:04d}"), f"{i:04d}")
                     for i, ch in enumerate(chs, 1)]
        lens, missing = [], []
        for i in range(1, len(chs) + 1):
            p = os.path.join(cards_dir, stems[i - 1] + ".md")
            if not os.path.exists(p):
                p = os.path.join(cards_dir, f"{i:04d}.md")
            t = self._read(p).strip()
            if len(t) < 80:
                missing.append(i)
            else:
                lens.append(n_hz(split_card(t)[0]))     # 只统计正文，不含人物简介
        head = [
            f"# {os.path.basename(task_dir).split('_', 2)[-1]} 全书章节总结",
            "",
            "## 质检",
            f"- 章数：{len(lens)} 篇（跳过空卡 {len(missing)} 章）",
            f"- 模型：{c['model']}　笔法：{c['style']}　温度：{c['temp']}",
            f"- 单章长度：最短 {min(lens) if lens else 0}／中位 "
            f"{sorted(lens)[len(lens)//2] if lens else 0}／最长 {max(lens) if lens else 0} 汉字"
            f"（目标区间 {c['card_lo']}–{c['card_hi']}）",
            f"- ⚠ 章（字数越界／引语／承接／漏写）：{warn} 篇；结算卡：每 {c['settle_every']} 章 1 张",
            "- 生成方式：事件行（时间/地点/人物/权重）→ 按地点聚场 → 原文素材句（带位置）→ "
            "按权重取舍的第三人称短文（开头承接上一张卡的落点、结尾写清本段落点）；"
            "引语回原文核验；每卡末尾附【本章重要人物】简介（含社会关系）；"
            "人物全量见 全书台账.md",
            "",
            "---",
            "",
        ]
        if ledger:
            top = sorted([v for v in ledger.values() if v["cat"] == "人物章"],
                         key=lambda v: -v["n"])[:20]
            if top:
                head += ["## 人物速查（按出现章数，全量见 全书台账.md）", "",
                         "| 人物 | 身份 | 首章 | 末章 | 出现 | 最新状态 |",
                         "|---|---|---|---|---|---|"]
                for v in top:
                    al = "、".join(sorted(x for x in (v.get("aliases") or ()) if x != v["name"]))
                    nm = v["name"] + (f"（{al}）" if al else "")
                    head.append(
                        f"| {nm} | {(v['role'] or '').replace('|', '／')} | "
                        f"{v['first']:03d} | {v['last']:03d} | {v['n']} | "
                        f"{(v['note'] or '').replace('|', '／')[:40]} |")
                head += ["", "---", ""]
        body = []
        for i, ch in enumerate(chs, 1):
            p = os.path.join(cards_dir, stems[i - 1] + ".md")
            if not os.path.exists(p):
                p = os.path.join(cards_dir, f"{i:04d}.md")
            t = self._read(p).strip()
            if len(t) < 80:
                continue
            if t.startswith("# "):                  # 卡片自带的标题行去掉，避免和 ## 重名
                t = "\n".join(t.split("\n")[1:]).strip()
            body.append(f"## {stems[i - 1]}")      # 汇总里的标题＝卡片文件名
            body.append("")
            body.append(t)
            body.append("")
        path = os.path.join(task_dir, "全书总结.md")
        open(path, "w", encoding="utf-8").write("\n".join(head + body))
        return path, len(lens)

    def _run(self, src, c):
        try:
            chs = self._load_chapters(src)
            if not chs:
                why = "没有找到任何章节"
                if os.path.isfile(src) and not self._read(src).strip():
                    why = ("读不出内容：文件是空的，或编码不是 UTF-8 / GBK / UTF-16"
                           "（可先用记事本另存为 UTF-8 再试）")
                self.ui(self._finish, False, why)
                return
            out, resumed = self.make_task_dir(c["out_dir"], src)
            self.last_task_dir = out
            for d in ("cards", "base", "verify", "ledger"):
                os.makedirs(os.path.join(out, d), exist_ok=True)
            ledger_dir = os.path.join(out, "ledger")
            ledger = {}
            for f in sorted(os.listdir(ledger_dir)):
                m = re.match(r"ch_(\d+)\.tsv$", f)
                if m:
                    self.merge_ledger(ledger, self._parse_ledger(
                        self._read(os.path.join(ledger_dir, f))), int(m.group(1)))
            total = len(chs)
            self.ui(self.log, ("续跑已有任务：" if resumed else "新建任务目录：") + out)
            self.ui(self.log, f"共 {total} 章｜普通卡 {c['card_lo']}–{c['card_hi']} 字｜"
                              f"结算卡 {c['base_lo']}–{c['base_hi']} 字｜每 {c['settle_every']} 章结算"
                              f"｜台账已有 {len(ledger)} 条")

            big = max((len(x["text"]) for x in chs), default=0)
            if big > 15000:
                self.ui(self.log, f"⚠ 最大一章 {big} 字：事件行上限 {c['ev_max']} 条装不下这么多内容，"
                                  f"建议把「事件行上限」提到 {min(200, max(20, big // 300))}、"
                                  f"「素材句数」提到 {min(90, max(8, big // 700))}；"
                                  f"或者先切段/分块再跑")
            book_cjk = cjk_only("".join(x["text"] for x in chs))
            # 卡片文件名 = 源文件名（章节目录则是每个 txt 的文件名主干），重名自动加序号
            stems, used = [], set()
            for i, ch in enumerate(chs, 1):
                st = safe_stem(ch.get("name") or ch.get("title") or f"{i:04d}", f"{i:04d}")
                base, k = st, 2
                while base in used:
                    base, k = f"{st}_{k}", k + 1
                used.add(base)
                stems.append(base)
            self._stems = stems

            # 「我」是谁：全书只判一次（叙述者.json），卡片统一第三人称
            narr = self._identify_narrator(c, out, chs, c.get("narrator", ""))
            nname = (narr.get("name") or "").strip()
            if nname:
                self.ui(self.log, f"叙述者：「我」＝{nname}"
                                  f"（{'手填' if narr.get('source') == 'manual' else '自动识别'}）"
                                  f"｜卡片统一第三人称")
            else:
                self.ui(self.log, "叙事人称：第三人称（本书没有第一人称叙述者）")

            def pov_head(pov):
                lab = {"first": "第一人称", "mixed": "第一/第三混合", "third": "第三人称"}
                return (f"人称 {lab.get(pov['verdict'], pov['verdict'])}"
                        f"（我 {pov['me']} 次、{pov['per1k']}/千字"
                        + (f"，第三人称段 {len(pov['spans'])} 处" if pov["spans"] else "") + "）")

            def cpath(no, ext=".md"):
                return os.path.join(out, "cards", stems[no - 1] + ext)

            def legacy(no, ext=".md"):        # 老任务用的是 0001.md，续跑时迁移过来
                old = os.path.join(out, "cards", f"{no:04d}{ext}")
                new = cpath(no, ext)
                if os.path.exists(old) and not os.path.exists(new):
                    try:
                        os.replace(old, new)
                    except Exception:
                        return old
                return new

            done = 0
            warn = 0
            warned_narr = False
            t0 = time.time()

            for i, ch in enumerate(chs, 1):
                if not self._gate():
                    self.ui(self._finish, False, f"已停止：完成 {done}/{total} 章，下次从第 {i} 章继续")
                    return
                no = i
                pov = detect_pov(ch["text"])
                # 整章第三人称时不把「我」映射成叙述者（那章的我可能根本不存在）
                narr_ch = "" if pov["verdict"] == "third" else nname
                if not nname and not warned_narr and pov["verdict"] != "third":
                    warned_narr = True
                    self.ui(self.log, "  ⚠ 本章是第一人称，但全书没识别出叙述者：卡片可能混用「我」；"
                                      "界面「叙述者」填名字后重跑")
                card_p = legacy(no)
                ev_p = legacy(no, ".events.md")

                # 断点续跑（台账缺的顺手补上，续跑不重复花钱）
                if (not c.get("rewrite")) and os.path.exists(card_p) and os.path.exists(ev_p) \
                        and os.path.getsize(card_p) > 100:
                    if not os.path.exists(os.path.join(ledger_dir, f"{no:04d}.tsv")):
                        self._fill_ledger(c, no, ch, self._read(ev_p), ledger, ledger_dir)
                    # 老卡没有人物简介 → 只补这一块，正文一个字节都不动（吃关系册保证一致）
                    if c.get("cast_enable", True) and CAST_HEAD not in self._read(card_p):
                        r0, _ = self._parse_events(self._read(ev_p))
                        if r0:
                            rel0 = self._load_rel(out)
                            hint = "\n".join(f"{k}：{v.get('text', '')}" for k, v in rel0.items()
                                             if k in cjk_only(ch["text"]))[
                                :max(800, 60 * int(c.get("cast_n", 6)))]
                            cr = self._make_cast(c, ch["title"], ledger,
                                                 self._clamp_rows(r0, c["ev_max"])[0],
                                                 hint, ch_text=ch["text"], narrator=narr_ch)
                            if cr:
                                cr, rel0, notes0 = self._fix_identity(cr, rel0, ch["text"], no)
                                rel0 = self._store_identity(rel0, cr, no)
                                self._save_rel(out, rel0)
                                _p0, _c0 = split_card(self._read(card_p))
                                open(card_p, "w", encoding="utf-8").write(
                                    card_text(stems[no - 1], cr, _p0))
                                self.ui(self.log, f"  第 {no} 章：补人物简介 {len(cr)} 人")
                                for nt in notes0:
                                    self.ui(self.log, f"  ⚖ {nt}")
                    done += 1
                    self.ui(self._progress, done, total, ch["title"])
                    continue

                # 前文：祖辈提要 + 上一章事件行 —— 只喂短文，不再喂事件行抽取
                prev_bases = [int(re.match(r"(\d+)", f).group(1)) for f in os.listdir(os.path.join(out, "base"))
                              if re.match(r"(\d+)", f)]
                prev_base = max([b for b in prev_bases if b < no], default=0)
                ti = ""
                if prev_base:
                    bp = self._read(os.path.join(out, "base", f"{prev_base:04d}.md"))
                    m = re.search(r"【祖辈提要】(.+?)(?=【)", bp, re.S)
                    ti = m.group(1).strip() if m else ""
                prev_ev = ""
                if no > 1:
                    prev_ev = self._read(legacy(no - 1, ".events.md")).strip()
                # 上一张卡的结尾 + 上一张卡的人物简介：卡与卡之间的桥
                prev_tail, prev_cast, prev_card = "", "", ""
                if no > 1:
                    prev_card = self._read(legacy(no - 1))
                    p_prose, p_cast = split_card(prev_card)
                    prev_tail = p_prose.strip()[-160:]
                    prev_cast = p_cast.replace(CAST_HEAD, "").strip()
                fg_parts = []
                if ti:
                    fg_parts.append("【祖辈提要】" + ti)
                if prev_ev:
                    fg_parts.append(f"【上一章（第{no-1}章）事件行】\n{prev_ev}")
                fg = "\n".join(fg_parts)

                self.ui(self.cur_chapter.set, f"{ch['title'][:24]}（{i}/{total}）")
                self.ui(self.log, f"第 {no} 章 {ch['title'][:24]}｜前文 {n_hz(fg)} 字"
                                  + (f"｜{pov_head(pov)}" if nname or pov["verdict"] != "third" else ""))

                # ① 事件行（只看本章正文：抽取器不该被前文污染）
                ev_user = f"【本章正文】\n{ch['title']}\n{ch['text']}"
                if narr_ch:
                    tip = (f"【叙事人称】第一人称：「我」＝{narr_ch}。\n"
                           f"1) 人物栏一律写名字，绝不许出现「我／我们／咱／俺」——「我」做的事记在"
                           f"{narr_ch} 名下；\n"
                           f"2) 描述里也把「我」写成{narr_ch}（引号里的台词照抄，不改）。\n")
                    if pov["spans"]:
                        tip += ("【本章的第三人称段落（主语是别人，不是" + narr_ch + "）】\n"
                                + "\n".join(f"- [{p}%] {s}" for p, s in pov["spans"]) + "\n")
                    ev_user = tip + ev_user
                ev, rows = None, None
                for a in range(c["attempts"]):
                    if not self._gate():
                        self.ui(self._finish, False, "已停止")
                        return
                    try:
                        t = self._call(c, [
                            {"role": "system", "content": SYS_EVENTS.format(n=c["ev_max"])},
                            {"role": "user", "content": ev_user}],
                            1200 + 60 * c["ev_max"])
                    except Exception as e:
                        self.ui(self.log, f"  事件行请求失败：{type(e).__name__}: {e}")
                        time.sleep(2)
                        continue
                    r, hard, soft = self._check_events(t, book_cjk, c["ev_max"], narrator=narr_ch)
                    self.ui(self.log, f"  事件行 试{a+1}: {len(r)} 条 {n_hz(t)} 字 "
                                      + ("✓" if not hard else "✗ " + str(hard)[:60]))
                    if not hard:
                        ev, rows = t, r
                        break
                if not ev:
                    self.ui(self.log, f"  ✗ 第 {no} 章事件行三轮不合格，停止（可修好后重跑，会跳过已完成章）")
                    self.ui(self._finish, False, f"停在第 {no} 章：事件行不合格")
                    return

                # ② 素材句（分箱取样，带原文位置百分比）
                material = self._pick_material(ch["text"], c["material"])
                qblock = "\n".join(f"- [{p}%] {q}" for p, q in material)
                # ③ 场景：先按权重截到 ev_max 条，再按地点聚场（清单式输入只会换回清单式输出）
                kept, dropped = self._clamp_rows(rows, c["ev_max"])
                scenes = self._group_scenes(kept)
                if dropped:
                    scenes += f"\n（另有 {dropped} 件低权重事件，可一句带过或略去）"
                    self.ui(self.log, f"  场景：事件行 {len(rows)} 条 → 取权重前 {len(kept)} 条"
                                      f"（丢 {dropped} 条）")
                # 本章出现过的人名（用来拦"串人"）
                ev_names = set()
                for r in rows:
                    m = re.search(r"人物\s*[:：]\s*([^|｜)）]+)", r["ctx"])
                    if m:
                        ev_names.update(p.strip() for p in
                                        re.split(r"[,，、;；/\s]+", m.group(1)) if p.strip())
                ch_cjk = cjk_only(ch["text"])
                offnames = [v["name"] for v in ledger.values()
                            if v["cat"] == "人物章" and len(v["name"]) >= 2
                            and v["name"] not in ev_names and v["name"] not in ch_cjk]

                # 必须写到（权重≥0.6 的事实，最多 6 条）：漏了会触发重写
                must, must_lines = [], []
                for r in [x for x in kept if x["w"] >= 0.6][:6]:
                    m2 = re.search(r"人物\s*[:：]\s*([^|｜)）]+)", r["ctx"])
                    names = set(p.strip() for p in re.split(r"[,，、;；/\s]+", m2.group(1))
                                if p.strip()) if m2 else set()
                    must.append((re.sub(r"\s+", "", r["desc"])[:16], names))
                    must_lines.append(f"- {r['desc'][:70]}")
                # 承接用：上一章最后几条事件里、本章还在场的人
                prev_names = []
                if prev_ev:
                    pn = set()
                    for m2 in re.finditer(r"人物\s*[:：]\s*([^|｜)）]+)",
                                          "\n".join(prev_ev.split("\n")[-3:])):
                        pn.update(p.strip() for p in re.split(r"[,，、;；/\s]+", m2.group(1))
                                  if p.strip())
                    prev_names = [n for n in pn if n in ev_names][:4]

                # ③.5 人物身份：先定身份（吃人物关系册 + 原文证据）→ 与关系册核验 → 才开始写正文
                rel = self._load_rel(out)
                id_rows, rel_map, id_block, rel_trip = [], {}, "", {}
                if c.get("cast_enable", True):
                    prev_cast2 = prev_cast
                    if rel:
                        keep_lines = [f"{k}：{v.get('text', '')}" for k, v in rel.items()
                                      if k in ev_names or k in ch_cjk]
                        if keep_lines:
                            prev_cast2 = "\n".join(keep_lines)[
                                :max(800, 60 * int(c.get("cast_n", 6)))]
                    id_rows = self._make_cast(c, ch["title"], ledger, kept, prev_cast2,
                                              ch_text=ch["text"], narrator=narr_ch)
                    if id_rows:
                        # 先查（吃关系册+原文证据）→ 写 → 验 → 错就纠 → 再验，通过了才写正文
                        for rnd in range(3):
                            id_rows, rel, notes = self._fix_identity(id_rows, rel, ch["text"], no)
                            for nt in notes:
                                self.ui(self.log, f"  ⚖ {nt}")
                            issues = self._audit_identity(id_rows, rel, ch["text"], narrator=narr_ch)
                            if not issues:
                                if rnd:
                                    self.ui(self.log, f"  ⚖ 身份核验通过（第 {rnd + 1} 轮）")
                                break
                            self.ui(self.log, "  ⚖ 身份待纠："
                                     + "；".join(f"{n}·{w}" for n, w in issues[:4]))
                            id_rows = self._repair_identity(id_rows, rel, ch["text"], issues, narrator=narr_ch)
                        rel = self._store_identity(rel, id_rows, no)
                        self._save_rel(out, rel)
                        self.ui(self.log, f"  人物身份 {len(id_rows)} 人：" +
                                "、".join(n for n, _ in id_rows))
                if id_rows:
                    id_block = "\n".join(f"- {n}：{d}" for n, d in id_rows)
                    rel_map = {n: set(rel.get(n, {}).get("claims") or ()) for n, _ in id_rows}
                    rel_map = {k: v for k, v in rel_map.items() if v}
                    # 关系册里本章在场的其他人也当硬约束（防写反）
                    for k, v in rel.items():
                        if k in ev_names or k in ch_cjk:
                            if v.get("claims"):
                                rel_map.setdefault(k, set(v["claims"]))
                            for kk, vv in (v.get("triples") or {}).items():
                                if vv:
                                    rel_trip[kk] = set(vv)

                # ④ 短文
                sys_prose = SYS_PROSE.format(
                    style=STYLE_RULES.get(c["style"], STYLE_RULES["混合"]),
                    quotes=QUOTE_RULES.get(c.get("quote_mode", "转述"), QUOTE_RULES["转述"]),
                    lo=c["card_lo"], hi=c["card_hi"],
                    mid=(c["card_lo"] + c["card_hi"]) // 2,
                    narr=(f"本书是第一人称叙述，原文的「我」＝{narr_ch}。全篇必须第三人称："
                          f"用「{narr_ch}」作主语，绝不许出现「我／我们／咱」（引号台词里可以有）；"
                          f"标了第三人称的段落，主语是别人，别把那些动作记到{narr_ch}头上。"
                          if narr_ch else
                          "本书是第三人称；全篇按人物名字写，不要用「我」叙述。"))
                best, best_score = None, 10 ** 9
                for a in range(c["attempts"]):
                    if not self._gate():
                        self.ui(self._finish, False, "已停止")
                        return
                    parts = [f"【本章】{ch['title']}", f"【场景事件】\n{scenes}",
                             f"【素材句】\n{qblock}"]
                    if narr_ch:
                        nb = (f"【叙述者】本章是第一人称，「我」＝{narr_ch}；正文用{narr_ch}作主语，"
                              f"全篇第三人称。")
                        if pov["spans"]:
                            nb += ("\n【第三人称段落（主语不是" + narr_ch + "）】\n"
                                   + "\n".join(f"- [{p}%] {s}" for p, s in pov["spans"]))
                        parts.append(nb)
                    if prev_tail:
                        parts.append("【上一张卡的结尾】\n…" + prev_tail)
                    if id_block:
                        parts.append("【人物身份（已核验，称谓与性别以此为准，不许写反）】\n"
                                     + id_block)
                    if must_lines:
                        parts.append("【本章必须写到】\n" + "\n".join(must_lines))
                    parts.append(f"【前文】\n{fg or '无（本书起始段）'}")
                    user = "\n\n".join(parts)
                    led = self._ledger_context(ledger, rows)
                    if led:
                        user += f"\n\n【台账】\n{led}"
                    if best and best[2]:
                        user += "\n\n上一版问题：" + "；".join(str(x) for x in best[2]) + "。请重写。"
                    try:
                        t = self._call(c, [{"role": "system", "content": sys_prose},
                                           {"role": "user", "content": user}], 2400)
                    except Exception as e:
                        self.ui(self.log, f"  短文请求失败：{type(e).__name__}: {e}")
                        time.sleep(2)
                        continue
                    hard, soft, hz, nq = self._check_prose(t, material, c, ch["text"], offnames,
                                                           prev_names=prev_names, must=must,
                                                           rel_map=rel_map, rel_trip=rel_trip, narrator=narr_ch)
                    self.ui(self.log, f"  短文 试{a+1}: {hz} 字 引文{nq} "
                                      + ("✓" if not hard and not soft else
                                         ("✗ " + str(hard)[:60] if hard else "⚠ " + str(soft)[:40])))
                    if not hard and not soft:
                        best = (t, hz, [])
                        break
                    score = (0 if not hard else 1000) + abs(hz - (c["card_lo"] + c["card_hi"]) // 2)
                    if score < best_score:
                        best, best_score = (t, hz, hard or soft), score
                    if not hard:
                        best = (t, hz, ["⚠ " + s for s in soft])
                        break

                txt = best[0]
                lines = txt.split("\n")
                if lines and re.match(r"^第[0-9零一二三四五六七八九十百]+章", lines[0].strip()):
                    txt = "\n".join(lines[1:]).lstrip("\n")
                # 硬校验没过 → 先试着程序修复引语（不重写整章），还不行才存草稿
                hard_left = [x for x in (best[2] or []) if not str(x).startswith("⚠")]
                if hard_left and all("引文" in str(x) for x in hard_left):
                    t2, nfix = self._repair_quotes(txt, ch["text"])
                    if nfix:
                        h2, s2, hz2, nq2 = self._check_prose(t2, material, c, ch["text"], offnames,
                                                             prev_names=prev_names, must=must,
                                                             rel_map=rel_map, rel_trip=rel_trip, narrator=narr_ch)
                        self.ui(self.log, f"  → 引语自动修复 {nfix} 处：" + ("✓" if not h2 else "仍有问题"))
                        if not h2:
                            txt = t2
                            best = (t2, hz2, ["⚠ " + x for x in s2])
                            hard_left = []
                dst = card_p
                if hard_left:
                    dst = os.path.join(out, "cards", "_draft", f"{stems[no - 1]}.md")
                    if os.path.exists(card_p):     # 旧稿挪走，免得汇总里混进没过校验的版本
                        old_dir = os.path.join(out, "cards", "_old")
                        os.makedirs(old_dir, exist_ok=True)
                        os.replace(card_p, os.path.join(old_dir, os.path.basename(card_p)))
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                open(dst, "w", encoding="utf-8").write(
                    card_text(os.path.splitext(os.path.basename(dst))[0], id_rows, txt))
                ev_saved = rows_text(rows) or ev
                open(ev_p, "w", encoding="utf-8").write(ev_saved)
                if hard_left:
                    self.ui(self.log, f"  → 存草稿（硬校验没过）：{os.path.relpath(dst, out)}")
                # ⑤ 台账：人物 × 章节
                self._fill_ledger(c, no, ch, ev_saved, ledger, ledger_dir)
                if best[2]:
                    warn += 1
                    json.dump({"issues": best[2], "汉字": best[1]},
                              open(os.path.join(out, "verify", f"{no:04d}.json"), "w", encoding="utf-8"),
                              ensure_ascii=False, indent=1)
                done += 1
                cost = time.time() - t0
                self.ui(self._progress, done, total, ch["title"])
                self.ui(self.stat_text.set,
                        f"已完成 {done}/{total}｜⚠ {warn}｜调用 {self.api_calls} 次｜"
                        f"用时 {cost/60:.1f} 分｜均 {cost/max(done,1):.0f}s/章")

                # ④ 结算卡
                if no % c["settle_every"] == 0 and self._gate():
                    seg = []
                    k = prev_base + 1
                    while k <= no:
                        ep = self._read(legacy(k, ".events.md"))
                        r2, _ = self._parse_events(ep)
                        if r2:
                            seg.append([k, r2])
                        k += 1
                    self.ui(self.log, f"  → 结算：{len(seg)} 章")
                    body = "\n".join(f"{s[0]}: " + " / ".join(x["desc"] for x in s[1]) for s in seg)
                    # 本段人物的已核验身份：直接取人物关系册，不重新猜
                    seg_ids, names_in = [], set()
                    if c.get("cast_enable", True) and seg:
                        for _, rs in seg:
                            for r in rs:
                                m3 = re.search(r"人物\s*[:：]\s*([^|｜)）]+)", r["ctx"])
                                if m3:
                                    names_in.update(p.strip() for p in
                                                    re.split(r"[,，、;；/\s]+", m3.group(1))
                                                    if p.strip())
                        relb = self._load_rel(out)
                        seg_ids = [(k, relb[k].get("text", "")) for k in relb
                                   if k in names_in and relb[k].get("text")][
                            :int(c.get("cast_n", 6))]
                    id_b = "\n".join(f"- {n}：{d}" for n, d in seg_ids)
                    sysb = SYS_BASE.format(ti=320, lo=c["base_lo"], hi=c["base_hi"])
                    btxt, bhard = None, None
                    for a in range(c["attempts"]):
                        if not self._gate():
                            break
                        try:
                            ucontent = (f"【旧祖辈提要】\n{ti or '无（本书起始段）'}\n\n"
                                        f"【事件行】\n{body}")
                            if id_b:
                                ucontent += ("\n\n【人物身份（已核验，称谓与性别以此为准）】\n" + id_b)
                            t = self._call(c, [{"role": "system", "content": sysb},
                                               {"role": "user", "content": ucontent}], 4000)
                        except Exception as e:
                            self.ui(self.log, f"  结算请求失败：{e}")
                            continue
                        hz = n_hz(t)
                        ok = ("【祖辈提要】" in t and "【本段记录】" in t
                              and c["base_lo"] <= hz <= c["base_hi"])
                        self.ui(self.log, f"  结算 试{a+1}: {hz} 字 " + ("✓" if ok else "✗ 超界或缺段"))
                        if ok:
                            btxt = t
                            break
                        btxt = btxt or t
                    if btxt:
                        bpath = os.path.join(out, "base", f"{no:04d}.md")
                        open(bpath, "w", encoding="utf-8").write(btxt)
                        if seg_ids and self.append_cast(bpath, seg_ids):
                            self.ui(self.log, f"  结算卡人物简介 {len(seg_ids)} 人（取自关系册）")

            # 收尾：索引 + 时间线
            index, timeline = [], []
            stem2no = {s: i for i, s in enumerate(stems, 1)}
            for f in sorted(os.listdir(os.path.join(out, "cards"))):
                if not f.endswith(".events.md"):
                    continue
                stem = f[:-len(".events.md")]
                no2 = stem2no.get(stem)
                if not no2:                      # 老命名 0001.events.md
                    m0 = re.match(r"(\d+)", stem)
                    no2 = int(m0.group(1)) if m0 else 0
                if not no2:
                    continue
                ep = os.path.join(out, "cards", f)
                rows, _ = self._parse_events(self._read(ep))
                for r in rows:
                    m = re.search(r"时间\s*[:：]\s*([^|｜)）]+)", r["ctx"])
                    timeline.append({"ch": no2,
                                     "idx": r["idx"],
                                     "time": m.group(1).strip() if m else "",
                                     "event": r["desc"], "w": r["w"]})
            json.dump(timeline, open(os.path.join(out, "timeline.json"), "w", encoding="utf-8"),
                      ensure_ascii=False, indent=1)

            # 粘合汇总版：标题 + 正文，一份 md 通读
            try:
                mp, cnt = self.build_merged_md(out, chs, c, warn, ledger, stems)
                self.ui(self.log, f"📘 汇总已生成：{os.path.basename(mp)}（{cnt} 章，"
                                  f"{os.path.getsize(mp)//1024} KB）")
            except Exception as e:
                self.ui(self.log, f"汇总生成失败：{e}")

            # 台账：人物 × 章节
            try:
                lp, pcnt = self.build_ledger_md(out, chs, stems)
                if lp:
                    self.ui(self.log, f"🗂 台账已生成：{os.path.basename(lp)}（{pcnt} 人）"
                                      f"＋台账_人物章节.tsv／台账_索引.json")
            except Exception as e:
                self.ui(self.log, f"台账生成失败：{e}")

            # 人物关系（已核验，跨章一致）
            try:
                relf = self._load_rel(out)
                if relf:
                    rl = ["# 人物关系（已核验）", "",
                          "| 人物 | 身份关系 | 最近更新章 |", "|---|---|---|"]
                    for k, v in sorted(relf.items(), key=lambda kv: -(kv[1].get("ch") or 0)):
                        rl.append(f"| {k} | {(v.get('text') or '').replace('|', '／')} | "
                                  f"{v.get('ch') or ''} |")
                    open(os.path.join(out, "人物关系.md"), "w", encoding="utf-8").write(
                        "\n".join(rl))
                    self.ui(self.log, f"👥 人物关系已生成：人物关系.md（{len(relf)} 人）")
            except Exception as e:
                self.ui(self.log, f"人物关系生成失败：{e}")

            sec = time.time() - t0
            self.ui(self._finish, True,
                    f"✅ 全部完成：{done}/{total} 章，⚠ {warn} 章，调用 {self.api_calls} 次，"
                    f"用时 {sec/60:.1f} 分\n\n结果目录：\n{out}\n\n"
                    f"（已生成 全书总结.md、全书台账.md、人物关系.md、台账_人物章节.tsv、台账_索引.json）")
        except Exception as e:
            import traceback
            traceback.print_exc()
            self.ui(self._finish, False, f"出错：{type(e).__name__}: {e}")

    def _progress(self, done, total, title=""):
        self.progress.set(done * 100.0 / max(total, 1))
        self.progress_text.set(f"{done} / {total}")
        if title:
            self.cur_chapter.set(title[:24])


def main():
    root = tk.Tk()
    app = LongSummaryApp(root)

    def on_close():
        if app.running:
            if not messagebox.askyesno("正在运行", "任务还在跑，确定要退出吗？\n（已完成的章节下次会自动跳过）"):
                return
            app.stop_event.set()
            app.run_event.set()
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_close)
    root.mainloop()


if __name__ == "__main__":
    main()
