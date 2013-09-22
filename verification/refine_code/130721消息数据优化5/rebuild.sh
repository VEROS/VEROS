make clean
make
/gnutools/arm-eabi/bin/arm-eabi-objcopy.exe -O srec main main.srec
/gnutools/arm-eabi/bin/arm-eabi-size.exe main
/gnutools/arm-eabi/bin/arm-eabi-size.exe main.srec
make clean
