#!/bin/bash
FILES="~/packagecrawler/*"
cnt=1
for f in $FILES
do
  if test "${f#*'.tgz'}" = "$f"
  then
    ./main.js $f
    cnt=$[$cnt + 1]
    echo $cnt
  fi
done
