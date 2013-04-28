#! /bin/sh
echo "***************   Starting computation  **********************"

j=0
for i in firstat_timeat firstat_progat sorted_sorted sorted_e_two member_t_insin member_t_insat member_firstat timel_insat_t erl_insin erl_insat erl_prog time_progat_er timeat_tcrt null_listat null_listat1 cons_insat cons_listat timel_listupto time_listat null_wind2 sorted_cons_listat timel_insin1 null_listupto1 erl_cons no_time sorted_insin2 timel_timeat_max progat_timel_erl  progat_insat1 sorted_listupto sorted_insat1 final progat_insat

do
j=`expr $j + 1`
echo "file $j: $i.spike"
    ../../../sources/spike_bc -dracula ../no_rm/$i.spike > $i.tmp
    echo "result written in $i.tmp" 
done
echo "***************   End computation  **********************"

