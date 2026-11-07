all:
	g++ -O2 -std=c++17 -I ../cadical/src alltarkies.cpp ../cadical/build/libcadical.a -o alltarkies