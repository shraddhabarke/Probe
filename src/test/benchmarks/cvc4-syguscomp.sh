#!/bin/bash

for f in string/*.sl; do
	STARTTIME=$(date +%s%N)
	out=`timeout 600 cvc4 --lang=sygus1 $f`
	ENDTIME=$(date +%s%N)
	ret=$(echo $out | tr '\r' '\n' | awk 'END{print}')
	strret=( $ret )
	ret=${ret//"unsat"/}
	diff=$(echo "scale=3; ($ENDTIME - $STARTTIME)/1000000000" | bc -l)   
	echo $f, $ret, ${#strret[@]},$diff
done