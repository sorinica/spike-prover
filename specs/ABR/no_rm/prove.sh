#! /bin/sh
echo "***************   Starting computation  **********************"

j=0
for i in cons_insat progat_insat1 cons_listat progat_insin_t erl_cons progat_timel_erl erl_insat erl_insin erl_prog sorted_cons_listat final sorted_e_cons firstat_progat sorted_e_insin firstat_timeat sorted_e_two leftmax_max sorted_insat1 listat_listupto sorted_insin2 listupto_t_insat sorted_listupto member_firstat sorted_sorted member_t_insat member_t_insin time_listat no_time time_progat_er null_listat timeat_tcrt null_listat1 timel_insat_t null_listupto1 timel_insin1 null_wind1 timel_listupto null_wind2 timel_timeat_max progat_insat

do
j=`expr $j + 1`
echo "file $j: $i.spike"
    ../../../sources/_build/default/spike.exe $i.spike > $i.tmp
    echo "result written in $i.tmp\n" 
done
echo "***************   End computation  **********************"

