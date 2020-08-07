#!/bin/bash

for f in string/*.sl; do
	STARTTIME=$(date +%s%N)
	out=`timeout 600 cvc4 --lang=sygus1 $f`
	ENDTIME=$(date +%s%N)
	ret=$(echo $out | tr '\r' '\n' | awk 'END{print}')
	strret=($ret)
	ret=${ret//"unsat"/}
	ite=$(echo $ret | grep -o 'ite' | wc -l)
	diff=$(echo "scale=3; ($ENDTIME - $STARTTIME)/1000000000" | bc -l)   
	examples=$(grep -c "constraint" $f)
	echo $f,$examples,$ret,$diff,$ite
done