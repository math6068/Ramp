all: ramp

ramp: ramp.cpp myHeap.h myBijection.h
	g++ -O3 -static ramp.cpp -o ramp

clean: rm -f *~
