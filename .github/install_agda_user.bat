@echo off
echo "Installing Agda for the current user..."

echo "Writing user paths ..."

setx Agda_datadir "%cd%\data"
setx PATH "%cd%\bin;%PATH%"

.\bin\agda.exe --version
if %errorlevel% neq 0 exit /b %errorlevel%

echo "Checking Agda.Primitive.agda..."

.\bin\agda.exe data\lib\prim\Agda\Primitive.agda
if %errorlevel% neq 0 exit /b %errorlevel%

echo "Agda is supposed to be installed now."
pause
