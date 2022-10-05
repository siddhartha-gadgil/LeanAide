#!/bin/bash

echo "Setting up _mathport_ for sentence translation" ...
echo "This script is meant to be run only once."
echo

# Variables
lean3repo="mathport_translation"

echo && echo Creating new _lean3_ repository $lean3repo ...
# the `lean3` version is hard-coded into the command
elan run leanprover-community--lean---3.48.0 leanproject new $lean3repo

echo && echo Modifying the _config_ file ...
# Edit the pathConfig.packages field of the config.json file to point to the above repository containing the Lean3 code
# Add ./Outputs/oleans/<repo_name> to pathConfig..leanPath in config.json
python3 -c "
import json

config = json.load(open('lean_packages/mathport/config.json', 'r'))

config['pathConfig']['packages']['$(echo $lean3repo | sed -r 's/(^|_)([a-z])/\U\2/g')'] = '../../$lean3repo/src'
config['pathConfig']['leanPath'].append('./Outputs/oleans/$lean3repo')

json.dump(config, open('lean_packages/mathport/config.json', 'w'), indent=4)
"

# Run make build, make source, and ./download_release nightly-2022-07-04 (the exact release can be altered to match the version of our repository)

cd lean_packages/mathport

echo && echo Building _mathport_ ...

make build

# this line may not be needed 
make source

#./download-release.sh $(awk -F: '{print $NF}' ../../lean-toolchain)
# Using the nightly release instead of the one in the lean-toolchain due to compatibility issues
./download-release.sh nightly-2022-10-02

lake build mathport