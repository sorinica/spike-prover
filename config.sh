#! /bin/sh

if [ "$#" -ne 1 ]; then
    echo "Give as argument the Coq version, one value from (8.4 to 8.19, except 8.7)"
    exit 2
fi

version=""
case  $1  in
               8.19)
     		    version="8.19"
                    ;;
               8.18)
     		    version="8.18"
                    ;;
               8.17)
     		    version="8.17"
                    ;;
               8.16)
     		    version="8.16"
                    ;;
               8.15)
     		    version="8.15"
                    ;;
               8.14)
     		    version="8.14"
                    ;;
               8.13)
     		    version="8.13"
                    ;;
               8.12)
     		    version="8.12"
                    ;;
               8.11)
     		    version="8.11"
                    ;;
               8.10)
     		    version="8.10"
                    ;;
               8.9)
     		    version="8.9"
                    ;;
               8.8)
     		    version="8.8"
                    ;;
               8.6)
     		    version="8.6"
                    ;;
               8.5)
     		    version="8.5"
                    ;;
               8.4)
     		    version="8.4"
                    ;;
                *)
                    echo "not a valid version. It should be a value from (8.4 to 8.19, except 8.7)"
                    exit 2
          esac 

CoqVersion="Coq"$version
rm theories/Coccinelle/Current
ln -s $CoqVersion theories/Coccinelle/Current
rm theories/CoLoR/Current
ln -s $CoqVersion theories/CoLoR/Current

echo "The Coccinelle and CoLoR libraries have been set for "$CoqVersion
