#! /bin/sh
echo "***************   Starting computation  **********************"

j=0
for i in sorted even_odd tree_list 

do
j=`expr $j + 1`
echo "file $j: $i.spike"
if [  "$1" == "-spec" ] ;then 
    ../../../sources/spike_bc -coqc_spec ../examples/$i.spike > $i.proof 
    echo "treating $i"'_spec.v' 
    time coqc "$i"'_spec.v' 
else 
    ../../../sources/spike_bc -coqc ../examples/$i.spike > $i.proof
    echo "treating $i.v" 
    time coqc "$i.v" 
fi
done
echo "***************   End computation  **********************"

