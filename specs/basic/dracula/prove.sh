#! /bin/sh
echo "***************   Starting computation  **********************"

j=0
for i in  even2odd sorted  tree_list even2odd_unoriented 

do
j=`expr $j + 1`
echo "file $j: $i.spike"
    ../../../sources/spike_bc -dracula ../examples/$i.spike > $i.tmp
    echo "result written in $i.tmp" 
done
echo "***************   End computation  **********************"

