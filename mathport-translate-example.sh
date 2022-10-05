#!/bin/bash

lean3repo="mathport_translation"

file_name="translation_test_example"
file_location="./data"

echo Input

echo && cat $file_location/$file_name.lean && echo

cp $file_location/$file_name.lean $lean3repo/src/ 

cd $lean3repo

echo && echo Starting translation && echo

lean --tlean --ast --make --recursive src/

cd ../lean_packages/mathport/

build/bin/mathport config.json $(echo $lean3repo | sed -r 's/(^|_)([a-z])/\U\2/g')::$file_name
#This is the same as
#build/bin/mathport config.json MathportTranslation::$file_name


echo && echo Translated output && echo

cat Outputs/src/$( echo $lean3repo | sed -E 's/[^a-z]+([a-z])/\U\1/gi;s/^([A-Z])/\l\1/')/$(echo $lean3repo | sed -r 's/(^|_)([a-z])/\U\2/g')/$(echo $file_name | sed -r 's/(^|_)([a-z])/\U\2/g').lean
# This is the same as
#cat Outputs/src/mathportTranslation/MathportTranslation/$FileName.lean

cd ../../$lean3repo/src/

rm $file_name.*
