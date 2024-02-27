#! /bin/bash
echo "***************   Starting computation  **********************"

j=0

for i in sorted even_odd tree_list 

do
j=`expr $j + 1`
echo "file $j: $i.spike"
    ../../../sources/_build/default/spike.exe -coqc_spec ../examples/$i.spike > $i.proof 
    ../../../sources/_build/default/spike.exe -coqc ../examples/$i.spike > $i.proof
done
echo "***************   End computation  **********************"

