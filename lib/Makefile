# Rules to compile the instrumentor

CC = clang
CXX  = clang++

#SOURCES = CommonSCCOps.cpp GenCondInfo.cpp WriteAliasCheck.cpp PMFencesChecker.cpp \
#					PMRedFlushesChecker.cpp PMModelVerifier.cpp
SOURCES = $(wildcard *.cpp)

OPTIMIZATION = -O2
CC_FLAGS =  `llvm-config --cflags --ldflags --libs --system-libs` -g $(OPTIMIZATION) -lm -fno-rtti -std=c++11

OBJECT_FILES = $(SOURCES:%.cpp=%.o)

EXEBASE = GenCondInfo
SHARED_LIB = $(addsuffix .so, $(EXEBASE))

.SUFFIXES: .o .cpp .so

.PHONY = all

all: $(OBJECT_FILES)
	$(CXX) -shared -o $(SHARED_LIB) $(OBJECT_FILES) -I../include $(CC_FLAGS)

%.o: %.cpp
	$(CXX) -o $@ -c $< -fPIC -w $(CC_FLAGS) -I../include

clean:
	rm -rf *.o *.so
