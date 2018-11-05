cmake_minimum_required(VERSION 3.10)

if(DEFINED ENV{VCPKG_ROOT} AND NOT DEFINED CMAKE_TOOLCHAIN_FILE)
    set(CMAKE_TOOLCHAIN_FILE "$ENV{VCPKG_ROOT}/scripts/buildsystems/vcpkg.cmake"
    CACHE STRING "")
endif()

project(LuaFullDump CXX)
set(CMAKE_CXX_STANDARD 17)

find_package(Lua REQUIRED)
find_package(fmt CONFIG REQUIRED)
    
add_executable(LuaFullDump main.cpp)
target_link_libraries(LuaFullDump PUBLIC ${LUA_LIBRARY}
 PRIVATE fmt::fmt fmt::fmt-header-only
 )
include_directories(${LUA_INCLUDE_DIR})