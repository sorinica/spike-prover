#! /bin/sh

if [ "$#" -ne 1 ]; then
    echo "Give as argument either Coq$number, with $number  a value from 8.14 to 8.20, or Rocq$number with $number equal to 9.0)"
    exit 2
fi

case $1  in
               Rocq9.0)
                    ;;
               Coq8.20)
                    ;;
               Coq8.19)
                    ;;
               Coq8.18)
                    ;;
               8.17)
                    ;;
               8.16)
                    ;;
               8.15)
                    ;;
               8.14)
                    ;;
               *)
                    echo "not a valid version. It should be a value from (Coq8.14 to Coq8.19, or Rocq9.0)"
                    exit 2
          esac 


rm theories/Coccinelle/Current
ln -s $1 theories/Coccinelle/Current
rm theories/CoLoR/Current
ln -s $1 theories/CoLoR/Current

echo "The Coccinelle and CoLoR libraries have been set for "$1
