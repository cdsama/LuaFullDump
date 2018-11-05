#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <string>
#include <lua.hpp>
#include <cstdint>
#include <fmt/format.h>
extern "C"
{
#include <lstate.h>
#include <lgc.h>
#include <lobject.h>
#include <ltable.h>
#include <lstring.h>
#include <lfunc.h>
}

struct ChildInfo
{
    std::string name;
    std::int32_t type;
};
using TChildrenMap = std::map<const void *, ChildInfo>;
using TLuaDumpMap = std::map<const void *, TChildrenMap>;

struct LuaDumpData
{
    TLuaDumpMap dumpmap;
    std::set<const void *> dumped;
};

#define hashpow2(t, n) (gnode(t, lmod((n), sizenode(t))))
#define hashstr(t, str) hashpow2(t, (str)->hash)
#define gnodelast(h) gnode(h, cast(size_t, sizenode(h)))
#define checkdeadkey(n) assert(!ttisdeadkey(gkey(n)) || ttisnil(gval(n)))

static const TValue *get_table_value(global_State *g, Table *et, int e)
{

    if (et == nullptr)
    {
        return nullptr;
    }

    if (((et)->flags & (1u << (e))) || novariant(et->tt) != LUA_TTABLE)
    {
        return nullptr;
    }
    TString *ename = g->tmname[e];
    Node *n = hashstr(et, ename);
    for (;;)
    { /* check whether 'key' is somewhere in the chain */
        const TValue *k = gkey(n);
        if (k && ttisshrstring(k) && eqshrstr(tsvalue(k), ename))
        {
            return gval(n); /* that's it */
        }
        else
        {
            int nx = gnext(n);
            if (nx == 0)
            {
                et->flags |= cast_byte(1u << e);
                return nullptr; /* not found */
            }
            n += nx;
        }
    }
}

static std::string value_to_string(global_State *g, const TValue *v)
{
    if (ttisboolean(v))
    {
        return bvalue(v) ? "true" : "false";
    }
    if (ttisinteger(v))
    {
        return fmt::format("{}", ivalue(v));
    }
    else if (ttisnumber(v))
    {
        return fmt::format("{}", fltvalue(v));
    }
    else if (ttisstring(v))
    {
        return fmt::format("\"{}\"", svalue(v));
    }
    else
    {
        return fmt::format("{}_{}", lua_typename(g->mainthread, ttnov(v)), (void *)gcvalue(v));
    }
}

static int a_lua_func(lua_State *L)
{
    return 0;
}

static int push_userdata_gc(lua_State *L)
{
    std::cout << lua_tostring(L, 1) << std::endl;
    return 0;
}

static int push_userdata(lua_State *L)
{
    lua_newuserdata(L, sizeof(std::int32_t));
    if (luaL_newmetatable(L, "push_userdata_mt"))
    {
        lua_pushcfunction(L, push_userdata_gc);
        lua_setfield(L, -2, "__gc");
    }
    lua_setmetatable(L, -2);
    return 1;
}

static void process_source(std::string &source)
{
    std::string search = "\n";
    std::string replace = "   ";
    size_t pos = 0;
    while ((pos = source.find(search, pos)) != std::string::npos)
    {
        source.replace(pos, search.length(), replace);
        pos += replace.length();
    }
    search = "  ";
    replace = "";
    pos = 0;
    while ((pos = source.find(search, pos)) != std::string::npos)
    {
        source.replace(pos, search.length(), replace);
        pos += replace.length();
    }
    auto showhalf = 25;
    if (source.length() > (showhalf * 2))
    {
        source = source.substr(0, showhalf) + " ... " + source.substr(source.length() - showhalf, showhalf);
    }
}

static void mark_object(LuaDumpData &dumpdata, global_State *g, const void *parent, const GCObject *obj, const std::string &name)
{
    if (obj == nullptr)
    {
        return;
    }
    auto &dumpmap = dumpdata.dumpmap;
    auto &dumped = dumpdata.dumped;
    auto objitr = dumped.find(obj);
    if (objitr != dumped.end())
    {
        return;
    }
    auto parentitr = dumpmap.find(parent);
    TChildrenMap *ParentschildrenMap = nullptr;
    if (parentitr == dumpmap.end())
    {
        ParentschildrenMap = &dumpmap[parent];
    }
    else
    {
        ParentschildrenMap = &parentitr->second;
    }

    (*ParentschildrenMap)[obj] = ChildInfo{name, novariant(obj->tt)};
    dumped.insert(obj);

    switch (obj->tt & 0x3F)
    {
    case LUA_TSHRSTR:
    {
        break;
    }
    case LUA_TLNGSTR:
    {
        break;
    }
    case LUA_TUSERDATA:
    {
        auto metatable = gco2u(obj)->metatable;
        if (metatable != nullptr)
        {
            mark_object(dumpdata, g, obj, obj2gco(metatable), "metatable_u");
        }
        TValue uvalue;
        getuservalue(g->mainthread, gco2u(obj), &uvalue);
        if (iscollectable(&uvalue))
        {
            mark_object(dumpdata, g, obj, gcvalue(&uvalue), "uservalue_u");
        }
        break;
    }
    case LUA_TLCL:
    {
        LClosure *cl = gco2lcl(obj);

        if (cl->p != nullptr)
        {
            mark_object(dumpdata, g, obj, obj2gco(cl->p), "luaclosure_proto");
        }
        else
        {
            break;
        }

        for (auto i = 0; i < cl->nupvalues; i++)
        { /* mark its upvalues */
            UpVal *uv = cl->upvals[i];
            if (uv != nullptr && iscollectable(uv->v))
            {
                TString *tsuvname = cl->p->upvalues[i].name;
                std::string suvname = (tsuvname == nullptr) ? "(*no name)" : getstr(tsuvname);
                mark_object(dumpdata, g, obj, gcvalue(uv->v), fmt::format("luaclosure_upval[{}:\"{}\"]", i, suvname));
            }
        }
        break;
    }
    case LUA_TCCL:
    {
        CClosure *cl = gco2ccl(obj);
        for (auto i = 0; i < cl->nupvalues; i++) /* mark its upvalues */
        {
            if (iscollectable(&cl->upvalue[i]))
            {
                mark_object(dumpdata, g, obj, gcvalue(&cl->upvalue[i]), fmt::format("cclosure_upval[{}]", i));
            }
        }
        break;
    }
    case LUA_TTABLE:
    {
        Table *h = gco2t(obj);

        if (h->metatable != nullptr)
        {
            mark_object(dumpdata, g, obj, obj2gco(h->metatable), "metatable_t");
        }

        char *weakkey = nullptr;
        char *weakvalue = nullptr;
        const TValue *mode = get_table_value(g, h->metatable, TM_MODE);

        if (mode && ttisstring(mode))
        {
            weakkey = strchr(svalue(mode), 'k');
            weakvalue = strchr(svalue(mode), 'v');
        }

        Node *n = nullptr;
        Node *limit = gnodelast(h);

        for (n = gnode(h, 0); n < limit; n++)
        { /* traverse hash part */
            checkdeadkey(n);
            if (!ttisnil(gval(n))) /* entry is empty? */
            {
                assert(!ttisnil(gkey(n)));

                if (weakkey == nullptr && iscollectable(gkey(n)))
                {

                    if (ttisstring(gkey(n)))
                    {
                        mark_object(dumpdata, g, obj, gcvalue(gkey(n)), fmt::format("tb_key:\"{}\"", svalue(gkey(n))));
                    }
                    else
                    {
                        mark_object(dumpdata, g, obj, gcvalue(gkey(n)), "tb_key");
                    }
                }
                if (weakvalue == nullptr && iscollectable(gval(n)))
                {
                    std::string skey = value_to_string(g, gkey(n));
                    if (skey == "\"__name\"")
                    {
                        mark_object(dumpdata, g, obj, gcvalue(gval(n)), fmt::format("tb_val[{}]:\"{}\"", skey, svalue(gval(n))));
                    }
                    else
                    {
                        mark_object(dumpdata, g, obj, gcvalue(gval(n)), fmt::format("tb_val[{}]", skey));
                    }
                }
            }
        }

        if (weakvalue == nullptr)
        {
            for (size_t i = 0; i < h->sizearray; i++)
            {
                if (iscollectable(&h->array[i]))
                {
                    mark_object(dumpdata, g, obj, gcvalue(&h->array[i]), fmt::format("arr[{}]", i + 1));
                }
            }
        }

        break;
    }
    case LUA_TTHREAD:
    {
        lua_State *th = gco2th(obj);
        StkId stkv = th->stack;
        if (stkv == nullptr)
        {
            break;
        }
        auto index = 0;
        for (; stkv < th->top; stkv++) /* mark live elements in the stack */
        {
            if (iscollectable(stkv))
            {
                mark_object(dumpdata, g, obj, gcvalue(stkv), fmt::format("stack[{}]", index));
            }
            index++;
        }

        break;
    }
    case LUA_TPROTO:
    {
        Proto *f = gco2p(obj);
        if (f->source != nullptr)
        {
            std::string source = getstr(f->source);
            process_source(source);
            mark_object(dumpdata, g, obj, obj2gco(f->source), fmt::format("proto_source:\"{}\"", source));
        }
        for (auto i = 0; i < f->sizek; i++) /* mark literals */
        {
            if (iscollectable(&f->k[i]))
            {
                mark_object(dumpdata, g, obj, gcvalue(&f->k[i]), fmt::format("proto_literal[{}]", i));
            }
        }
        for (auto i = 0; i < f->sizeupvalues; i++) /* mark upvalue names */
        {
            mark_object(dumpdata, g, obj, obj2gco(f->upvalues[i].name), fmt::format("proto_uvname[{}]:\"{}\"", i, getstr(f->upvalues[i].name)));
        }
        for (auto i = 0; i < f->sizep; i++) /* mark nested protos */
        {
            mark_object(dumpdata, g, obj, obj2gco(f->p[i]), fmt::format("nested_proto[{}]", i));
        }
        for (auto i = 0; i < f->sizelocvars; i++) /* mark local-variable names */
        {
            mark_object(dumpdata, g, obj, obj2gco(f->locvars[i].varname), fmt::format("proto_locname[{}]:\"{}\"", i, getstr(f->locvars[i].varname)));
        }
        break;
    }
    default:
    {
        std::cout << (int)obj->tt << std::endl;
        assert(false);
        break;
    }
    }
}

static void full_dump_lua(lua_State *L)
{
    LuaDumpData dumpdata;
    global_State *g = G(L);
    mark_object(dumpdata, g, g, obj2gco(g->mainthread), "mainthread");
    mark_object(dumpdata, g, g, gcvalue(&g->l_registry), "registry");
    {
        auto threadindex = 0;
        lua_State *thread = g->twups;
        while (thread != nullptr)
        {
            threadindex++;
            UpVal *uv;
            mark_object(dumpdata, g, g, obj2gco(thread), fmt::format("thread[{}]", threadindex));
            auto uvindex = 0;
            for (uv = thread->openupval; uv != NULL; uv = uv->u.open.next)
            {
                uvindex++;
                if (iscollectable(uv->v))
                {
                    mark_object(dumpdata, g, g, gcvalue(uv->v), fmt::format("thread[{}]uv[{}]", threadindex, uvindex));
                }
            }

            if (thread == thread->twups)
            {
                break;
            }
            thread = thread->twups;
        }
    }

    for (auto &pair : dumpdata.dumpmap)
    {

        for (auto &i : pair.second)
        {
            std::cout << fmt::format(":{}->{}:{:<9}{{{}}}",
                                     pair.first,
                                     i.first,
                                     lua_typename(L, i.second.type),
                                     i.second.name)
                      << std::endl;
        }
    }
}

int main(int argc, char const *argv[])
{
    lua_State *L = luaL_newstate();
    luaL_openlibs(L);
    lua_pushcfunction(L, push_userdata);
    lua_setglobal(L, "push_userdata");
    luaL_loadstring(L, R"^^(
        local tb = {}
        setmetatable(tb, {__mode = "v"})
        local tb2 = {a=1}
        tb.str = tb2
        tb2 = nil
        collectgarbage()
        local c = 0
        for k,v in pairs(tb)
        do
            print(k, v)
            c = c + 1
        end
        setmetatable(debug.getregistry(), {{a=1},{b=2}})
        func = function()
            print("aa")
        end

        local uv = push_userdata()
        co2 = coroutine.create(
        function()
            for i=1,10 do
                print(i)
                print(uv)
                if i == 3 then
                    print(coroutine.status(co2))  --running
                    print(coroutine.running()) --thread:XXXXXX
                end
                coroutine.yield()
            end
        end
        )
        _G=_G
        coroutine.resume(co2) --1
        coroutine.resume(co2) --2
        uv2 = push_userdata()
        print(c)
        )^^");

    if (lua_pcall(L, 0, LUA_MULTRET, 0))
    {
        std::cout << lua_tostring(L, -1) << std::endl;
    }
    lua_pushstring(L, "haha");
    lua_pushcclosure(L, a_lua_func, 1);
    lua_pushstring(L, "haha");
    std::cout << lua_gettop(L) << std::endl;
    full_dump_lua(L);
    lua_close(L);
    return 0;
}
