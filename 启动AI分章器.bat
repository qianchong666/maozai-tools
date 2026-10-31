@echo off
chcp 65001 >nul
cd /d "%~dp0"
if exist ".venv\Scripts\python.exe" (
    ".venv\Scripts\python.exe" "猫仔AI分章器.py"
) else (
    python "猫仔AI分章器.py"
)
if errorlevel 1 (
    echo.
    echo Program exited with an error. Press any key to close...
    pause >nul
)
