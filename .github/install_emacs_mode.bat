@echo off

echo "Installing Agda's Emacs mode..."

.\bin\agda-mode.exe setup
if %errorlevel% neq 0 exit /b %errorlevel%
.\bin\agda-mode.exe compile
if %errorlevel% neq 0 exit /b %errorlevel%

echo "Done."
