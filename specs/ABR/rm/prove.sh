#! /bin/sh
echo "***************   Starting computation  **********************"

j=0
for i in cons_insat progat_insat cons_listat progat_insat1 erl_cons progat_insin_t erl_insat progat_insin_timeat erl_insin progat_listupto erl_prog progat_timel_erl final right_wind firstat_progat sorted_cons_listat firstat_timeat sorted_e_cons leftmax_max sorted_e_insin listat_listupto sorted_e_listupto listupto1_erl sorted_e_two listupto_t_insat sorted_insat1 member_firstat sorted_insin2 member_t_insat sorted_listupto member_t_insin sorted_sorted member_t_timel time_listat no_time time_progat_er null_listat timeat_tcrt null_listat1 timel_insat_t null_listupto timel_insin1 null_listupto1 timel_listupto null_wind1 timel_timeat_max  

do
j=`expr $j + 1`
echo "file $j: $i.spike"
    ../../../sources/spike_bc $i.spike > $i.tmp
    echo "result written in $i.tmp\n" 
done
echo "***************   End computation  **********************"

