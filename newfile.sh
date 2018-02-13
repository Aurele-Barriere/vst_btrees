~/CompCert/clightgen myprogs/$1.c

coqc `cat .loadpath-export` myprogs/$1.v

touch myprogs/verif_$1.v
