all: 
	cd src; make nc; make htdoc; cd ..; mv ./src/doc/dprle/html ./doc; mv ./src/dprle ./bin/

clean: 
	rm -r ./doc/* ./bin/*; cd src; make clean; make clean-doc; cd ..