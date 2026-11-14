test:
	g++ -O2 -std=c++17 -I ../cadical/src alltarkies.cpp ../cadical/build/libcadical.a -o alltarkies

perf:
	g++ -O2 -DNDEBUG -std=c++17 -I ../cadical/src alltarkies.cpp ../cadical/build/libcadical.a -o alltarkies

ji:
	g++ -O2 -std=c++17 -I ../cadical/src ji-autarkies.cpp ../cadical/build/libcadical.a -o ji-autarkies