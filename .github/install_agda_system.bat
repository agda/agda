@echo off
echo "Installing Agda for all users..."

echo "Writing system paths ..."

setx /M Agda_datadir "%cd%\data"
setx /M PATH "%cd%\bin;%PATH%"

.\bin\agda.exe --version
if %errorlevel% neq 0 exit /b %errorlevel%

echo "Checking Agda.Primitive.agda..."

.\bin\agda.exe data\lib\prim\Agda\Primitive.agda
if %errorlevel% neq 0 exit /b %errorlevel%

echo "Agda is supposed to be installed now."
pause
