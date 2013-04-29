#! /bin/sh
echo "***************   Starting computation  **********************"

j=0

if [ ! -f utils.vo ] ; then
    echo "... building utils.vo"
    coqc utils.v
fi

if [ ! -f coccinelle_utils.vo ] ; then
    echo "... building coccinelle_utils.vo"
    coqc coccinelle_utils.v
fi

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

