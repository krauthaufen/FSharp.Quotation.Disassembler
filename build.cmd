@echo off
echo %~dp0

PUSHD %~dp0
cls

IF exist packages\FAKE ( echo skipping FAKE download ) ELSE ( 
echo downloading FAKE
REM mklink .\.git\hooks\pre-commit .\pre-commit
"packages\nuget.exe" "install" "FAKE" "-OutputDirectory" "packages" "-ExcludeVersion" "-Prerelease"
"packages\nuget.exe" "install" "FSharp.Formatting.CommandTool" "-OutputDirectory" "packages" "-ExcludeVersion" "-Prerelease"
"packages\nuget.exe" "install" "SourceLink.Fake" "-OutputDirectory" "packages" "-ExcludeVersion"
"packages\nuget.exe" "install" "NUnit.Runners" "-OutputDirectory" "packages" "-ExcludeVersion"
)

SET TARGET="Default"

IF NOT [%1]==[] (set TARGET="%1")

"packages\FAKE\tools\Fake.exe" "build.fsx" "target=%TARGET%"

REM IF NOT [%1]==[] (set TARGET="%1")
REM "tools\FAKE\tools\Fake.exe" "build.fsx" "target=%TARGET%" %*