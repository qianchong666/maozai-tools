@echo off
chcp 65001 >nul
cd /d "%~dp0"
if exist ".venv\Scripts\python.exe" (
    ".venv\Scripts\python.exe" "猫仔长文总结器.py"
) else (
    python "猫仔长文总结器.py"
)
if errorlevel 1 (
    echo.
    echo Program exited with an error. Press any key to close...
    pause >nul
)
