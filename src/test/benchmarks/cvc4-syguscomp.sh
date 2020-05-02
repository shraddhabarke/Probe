#!/bin/bash

for f in euphony/*.sl; do
	STARTTIME=$(date +%s%N)
	out=`timeout 600 /c/users/shrad/downloads/cvc4-1.7-win64-opt.exe $f`
	ENDTIME=$(date +%s%N)
	ret=$(echo $out | tr '\r' '\n' | awk 'END{print}')
	strret=( $ret )
	echo ${#strret[@]},$((($ENDTIME - $STARTTIME)/1000000000)),$ret
done