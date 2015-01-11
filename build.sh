#!/bin/bash

if [ ! -d "packages/FAKE" ]; then
	echo "downloading FAKE"
	mono --runtime=v4.0 packages/nuget.exe install FAKE -OutputDirectory packages -ExcludeVersion
	mono --runtime=v4.0 packages/nuget.exe install FSharp.Formatting.CommandTool -OutputDirectory packages -ExcludeVersion -Prerelease 
	mono --runtime=v4.0 packages/nuget.exe install SourceLink.Fake -OutputDirectory packages -ExcludeVersion 
    mono --runtime=v4.0 packages/nuget.exe install NUnit.Runners -OutputDirectory packages -ExcludeVersion 
fi


mono packages/FAKE/tools/FAKE.exe "build.fsx"  $@

