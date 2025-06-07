include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"

module CausalMesh_Cache_i {
    import opened Collections__Maps_i
    import opened CausalMesh_Types_i
    import opened CausalMesh_Message_i
    import opened Environment_s

    function Circle(id:int, nodes:int) : (i:int)
        requires 0 <= id < nodes
        ensures 0 <= i < nodes
    {
        if nodes == 1 then 
            id
        else if id == nodes - 1 then
            0
        else
            id + 1
    }

    function GetDeps(icache:ICache, deps:Dependency, todos:set<(Key, VectorClock)>, domain:set<Key>) : (res:set<(Key, VectorClock)>)
        // requires ICacheValid(icache)
        requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                    && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
        requires DependencyValid(deps)
        requires forall k :: k in icache ==> k in domain
        requires forall k :: k in deps ==> k in domain
        requires forall kv :: kv in todos ==> kv.0 in domain && kv.0 in Keys_domain
        // requires forall k :: k in deps ==> k in icache
        requires forall kv :: kv in todos ==> VectorClockValid(kv.1) // && kv.0 in icache
        ensures forall kv :: kv in res ==> VectorClockValid(kv.1) && kv.0 in domain && kv.0 in Keys_domain
        decreases |icache|, |deps| 
    {
        if |deps| == 0 then 
            todos
        else 
            var k :| k in deps;
            var new_deps := RemoveElt(deps, k);
            assert |new_deps| < |deps|;
            if (k, deps[k]) in todos then
                GetDeps(icache, new_deps, todos, domain)
            else if !(k in icache) then // why?
                GetDeps(icache, new_deps, todos, domain)
            else if exists m :: m in icache[k] && VCEq(m.vc, deps[k]) then 
                var m :| m in icache[k] && VCEq(m.vc, deps[k]);
                var new_cache := RemoveElt(icache, k); // is this right?
                assert |new_cache| < |icache|;
                var updatedTodos := todos + {(k, deps[k])};
                var recursive := GetDeps(new_cache, m.deps, updatedTodos, domain);
                GetDeps(icache, new_deps, recursive, domain)
            else
                GetDeps(icache, new_deps, todos + {(k, deps[k])}, domain)
    }

    function MergeTodos(todos:set<(Key, VectorClock)>, deps:Dependency) : (res:Dependency)
        requires forall kv :: kv in todos ==> VectorClockValid(kv.1) && kv.0 in Keys_domain
        requires DependencyValid(deps)
        ensures DependencyValid(res)
        ensures forall k :: k in res ==> (exists kv :: kv in todos && kv.0 == k) || (exists k2 :: k2 in deps && k2 == k)
        decreases |todos|
    {
        if |todos| == 0 then 
            deps
        else
            var todo :| todo in todos;
            var key := todo.0;
            var vc := todo.1;
            if key in deps then 
                var new_deps := deps[key := VCMerge(deps[key], vc)];
                MergeTodos(todos - {todo}, new_deps)
            else 
                var new_deps := deps[key := vc];
                MergeTodos(todos - {todo}, new_deps)
    } 

    function RemoveNotLarger(bk:set<Meta>, vc:VectorClock, bk_res:set<Meta>, res:Meta, domain:set<Key>) : (r:(set<Meta>, Meta))
        requires forall m :: m in bk ==> MetaValid(m) && m.key == res.key && (forall kk :: kk in m.deps ==> kk in domain)
        requires VectorClockValid(vc)
        requires forall m :: m in bk_res ==> MetaValid(m) && m.key == res.key && (forall kk :: kk in m.deps ==> kk in domain)
        requires MetaValid(res)
        // ensures var r := RemoveNotLarger(bk, vc, bk_res, res);
        ensures forall m :: m in r.0 ==> MetaValid(m) && m.key == res.key && (forall kk :: kk in m.deps ==> kk in domain)
        ensures MetaValid(r.1)
        ensures forall m :: m in bk ==> m.key == r.1.key
        decreases |bk|
    {
        if |bk| == 0 then 
            (bk_res, res)
        else 
            var m :| m in bk;
            if VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc) then 
                RemoveNotLarger(bk - {m}, vc, bk_res, MetaMerge(res, m), domain)
            else 
                RemoveNotLarger(bk - {m}, vc, bk_res + {m}, res, domain)
    }

    // function PullTodos(icache:ICache, ccache:CCache, todos:set<(Key, VectorClock)>) : (ICache, CCache)
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     requires forall kv :: kv in todos ==> VectorClockValid(kv.1) && kv.0 in icache && kv.0 in ccache // is this true?
    //     ensures var c := PullTodos(icache, ccache, todos);
    //             && ICacheValid(c.0)
    //             && CCacheValid(c.1)
    //     decreases |todos|
    // {
    //     if |todos| == 0 then 
    //         (icache, ccache)
    //     else 
    //         var kv :| kv in todos;
    //         var vc := kv.1;
    //         var k := kv.0;
    //         var metas := icache[k];
    //         var init := Meta(k, 0, EmptyVC(), map[]);
    //         var pair := RemoveNotLarger(metas, vc, {}, init);
    //         assert MetaValid(pair.1);
    //         assert forall m :: m in metas ==> m.key == pair.1.key;
    //         var updated_icache := icache[k := pair.0];
    //         var updated_ccache := ccache[k := MetaMerge(ccache[k], pair.1)];
    //         PullTodos(updated_icache, updated_ccache, todos - {kv})
    // }

    function PullTodos(icache:ICache, ccache:CCache, todos:Dependency) : (c:(ICache, CCache))
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires DependencyValid(todos) 
        requires forall k :: k in todos ==> k in icache 
        // requires forall k :: k in todos ==> k in ccache // is this true?
        // ensures var c := PullTodos(icache, ccache, todos);
        ensures ICacheValid(c.0)
        ensures CCacheValid(c.1)
        // ensures forall k :: k in todos ==> k in c.0 && k in c.1
        ensures forall k :: k in icache ==> k in c.0
        ensures forall k :: k in ccache ==> k in c.1
        decreases |todos|
    {
        if |todos| == 0 then 
            (icache, ccache)
        else 
            var k :| k in todos;
            var vc := todos[k];
            var metas := icache[k];
            var init := Meta(k, EmptyVC(), map[]);
            var domain := icache.Keys;
            var pair := RemoveNotLarger(metas, vc, {}, init, domain);
            assert MetaValid(pair.1);
            assert forall m :: m in metas ==> m.key == pair.1.key;
            assert forall kv :: kv in pair.0 ==> forall kk :: kk in kv.deps ==> kk in icache;
            var updated_icache := icache[k := pair.0];
            // var updated_ccache := ccache[k := MetaMerge(ccache[k], pair.1)];
            var updated_ccache := InsertIntoCCache(ccache, pair.1); // this is different with the TLA+ spec
            PullTodos(updated_icache, updated_ccache, RemoveElt(todos, k))
    }

    function PullDeps(icache:ICache, ccache:CCache, deps:Dependency) : (c:(ICache, CCache))
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in ccache ==> k in icache
        requires DependencyValid(deps)
        requires forall k :: k in deps ==> k in icache && k in ccache
        ensures ICacheValid(c.0)
        ensures CCacheValid(c.1)
    {
        var domain := icache.Keys + deps.Keys;
        var todos := GetDeps(icache, deps, {}, domain);
        assert forall kv :: kv in todos ==> kv.0 in icache;
        var merged := MergeTodos(todos, map[]);
        assert forall k :: k in merged ==> exists kv :: kv in todos && kv.0 == k;
        assert forall k :: k in merged ==> k in icache;
        PullTodos(icache, ccache, merged)
    }



    // function GetDeps2(icache:ICache, deps:Dependency, todos:Dependency, domain:set<Key>) : (res:Dependency)
    //     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
    //                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    //     requires DependencyValid(deps)
    //     requires forall k :: k in icache ==> k in domain
    //     // requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    //     requires forall k :: k in deps ==> k in domain
    //     requires forall k :: k in todos ==> k in domain && k in Keys_domain && VectorClockValid(todos[k])
    //     ensures DependencyValid(res)
    //     ensures forall k :: k in res ==> k in domain
    //     ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k], res[k]) || VCEq(todos[k], res[k]))
    //     // ensures forall k :: k in deps ==> k in res
    //     decreases |icache|, |deps|
    // {
    //     if |deps| == 0 then 
    //         todos 
    //     else 
    //         var k :| k in deps;
    //         var new_deps := RemoveElt(deps, k);
    //         if k in todos && (VCHappendsBefore(deps[k], todos[k]) || VCEq(deps[k], todos[k])) then 
    //             GetDeps2(icache, new_deps, todos, domain)
    //         else if !(k in icache) then 
    //             GetDeps2(icache, new_deps, todos, domain)
    //         else 
    //             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
    //             var initial := EmptyMeta(k);
    //             assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
    //             var merged := FoldMetaSet(initial, metas, domain);

    //             lemma_FoldMetaBounded(initial, metas, deps[k], domain);
    //             assert VCHappendsBefore(merged.vc, deps[k]) || VCEq(merged.vc, deps[k]);
    //             assert forall kk :: kk in merged.deps ==> kk in domain;
    //             // var updaetd := GetDeps2(icache, merged.deps, )
    //             var todos' := DependencyInsertOrMerge(todos, k, merged.vc);

    //             // assert VCHappendsBefore(todos'[k], deps[k]) || VCEq(todos'[k], deps[k]);

    //             var new_cache := RemoveElt(icache, k); // is this right?
    //             var res := GetDeps2(new_cache, merged.deps, todos', domain);

    //             assert forall k :: k in todos' ==> k in res && (VCHappendsBefore(todos'[k], res[k]) || VCEq(todos'[k], res[k]));

    //             // var final := DependencyMerge(todos', res);
    //             // lemma_DependencyMergeDominatedByTheLargerOne(todos', res);
    //             // assert final == res;
    //             // var final := DependencyInsertOrMerge(added2, k, merged.vc);
    //             GetDeps2(icache, new_deps, res, domain)
    // }

    function GetDeps2(icache:ICache, deps:Dependency, todos:Dependency, domain:set<Key>) : (res:Dependency)
        requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                    && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
        requires DependencyValid(deps)
        requires forall k :: k in icache ==> k in domain
        // requires forall k :: k in Keys_domain ==> k in icache // should we have this?
        requires forall k :: k in deps ==> k in domain
        requires forall k :: k in todos ==> k in domain && k in Keys_domain && VectorClockValid(todos[k])
        ensures DependencyValid(res)
        ensures forall k :: k in res ==> k in domain
        ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k], res[k]) || VCEq(todos[k], res[k]))
        // ensures forall k :: k in deps ==> k in res
        decreases |icache.Values|, |deps|
    {
        if |deps| == 0 then 
            todos 
        else 
            var k :| k in deps;
            var new_deps := RemoveElt(deps, k);
            if k in todos && (VCHappendsBefore(deps[k], todos[k]) || VCEq(deps[k], todos[k])) then 
                GetDeps2(icache, new_deps, todos, domain)
            else if !(k in icache) then 
                GetDeps2(icache, new_deps, todos, domain)
            else 
                var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
                if |metas| > 0 then
                    var initial := EmptyMeta(k);
                    assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
                    var merged := FoldMetaSet(initial, metas, domain);

                    lemma_FoldMetaBounded(initial, metas, deps[k], domain);
                    assert VCHappendsBefore(merged.vc, deps[k]) || VCEq(merged.vc, deps[k]);
                    assert forall kk :: kk in merged.deps ==> kk in domain;
                    // var updaetd := GetDeps2(icache, merged.deps, )
                    var todos' := DependencyInsertOrMerge(todos, k, merged.vc);

                    // assert VCHappendsBefore(todos'[k], deps[k]) || VCEq(todos'[k], deps[k]);

                    // var new_cache := RemoveElt(icache, k); // is this right?
                    var new_cache := icache[k:= icache[k] - metas];
                    assert icache[k] >= metas;
                    lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
                    assert |new_cache.Values| < |icache.Values|;

                    var res := GetDeps2(new_cache, merged.deps, todos', domain);

                    assert forall k :: k in todos' ==> k in res && (VCHappendsBefore(todos'[k], res[k]) || VCEq(todos'[k], res[k]));

                    // var final := DependencyMerge(todos', res);
                    // lemma_DependencyMergeDominatedByTheLargerOne(todos', res);
                    // assert final == res;
                    // var final := DependencyInsertOrMerge(added2, k, merged.vc);
                    GetDeps2(icache, new_deps, res, domain)
                else 
                    GetDeps2(icache, new_deps, todos, domain)
    }

    

    function PullDeps2(icache:ICache, ccache:CCache, deps:Dependency) : (c:(ICache, CCache))
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in ccache ==> k in icache
        requires DependencyValid(deps)
        requires forall k :: k in deps ==> k in icache // && k in ccache
        ensures ICacheValid(c.0)
        ensures CCacheValid(c.1)
        // ensures forall k :: k in deps ==> k in c.0 && k in c.1
        ensures forall k :: k in icache ==> k in c.0
        ensures forall k :: k in ccache ==> k in c.1
    {
        var domain := icache.Keys + deps.Keys;
        var todos := GetDeps2(icache, deps, map[], domain);
        PullTodos(icache, ccache, todos)
    }


    function FoldMetaIntoICache(icache: ICache, metas: set<Meta>): ICache
        requires ICacheValid(icache)
        requires forall m :: m in metas ==> MetaValid(m) && (forall kk :: kk in m.deps ==> kk in Keys_domain && kk in icache)
        decreases |metas|
    {
        if metas == {} then 
            icache
        else 
            var m: Meta :| m in metas;
            FoldMetaIntoICache(AddMetaToICache(icache, m), metas - {m})
    }


    function AdvanceVC(vc:VectorClock, i:int) : (res:VectorClock)
        requires VectorClockValid(vc)
        requires 0 <= i < Nodes 
        ensures VectorClockValid(res)
    {
        vc[i:=vc[i]+1]
    }


    /** Key Properties */

    predicate CausalCut(ccache: CCache)
        requires CCacheValid(ccache)
    {
        forall k :: k in ccache ==>
            forall kk :: kk in ccache[k].deps ==>
                kk in ccache &&
                (VCHappendsBefore(ccache[k].deps[kk], ccache[kk].vc) || VCEq(ccache[k].deps[kk], ccache[kk].vc))
    }

    predicate ReadsDepsAreMet(icache:ICache, ccache:CCache, deps:Dependency)
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> 
            var m := FoldMetaSet(ccache[k], icache[k], icache.Keys);
            VCEq(deps[k], m.vc) || VCHappendsBefore(deps[k], m.vc)
    }

    predicate UponReadsDepsAreMet(ccache:CCache, deps:Dependency)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> 
            VCEq(deps[k], ccache[k].vc) || VCHappendsBefore(deps[k], ccache[k].vc)
    }


    /** Actions */
    datatype Server = Server(
        id : int,
        gvc : VectorClock,
        next : int,
        icache : ICache,
        ccache : CCache
    )

    predicate ServerValid(s:Server)
    {
        && 0 <= s.id < Nodes
        && 0 <= s.next < Nodes
        && VectorClockValid(s.gvc)
        && ICacheValid(s.icache)
        && CCacheValid(s.ccache)
        && forall k :: k in Keys_domain ==> k in s.icache && k in s.ccache
        && forall k :: k in s.ccache ==> k in s.icache
    }


    function InitICache(): ICache
    {
        map k | k in Keys_domain :: {EmptyMeta(k)}
    }

    function InitCCache(): CCache
    {
        map k | k in Keys_domain :: EmptyMeta(k)
    }

    predicate ServerInit(s:Server, id:int)
        requires 0 <= id < Nodes
    {
        && s.id == id
        && s.next == Circle(id, Nodes)
        && s.gvc == EmptyVC()
        && s.icache == InitICache()
        && s.ccache == InitCCache()
    }

    predicate ReceiveRead(s:Server, s':Server, p:Packet, sp:seq<Packet>)
        requires p.msg.Message_Read?
        requires ServerValid(s)
        requires PacketValid(p)
        // ensures ServerValid(s')
    {
        var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, p.msg.deps_read);
        && s' == s.(icache := new_icache, ccache := new_ccache)
        && sp == [LPacket(s.id, p.src, 
                        Message_Read_Reply(
                            p.msg.key_read,
                            new_ccache[p.msg.key_read].vc,
                            new_ccache[p.msg.key_read].deps
                        )
                    )]
    }

    predicate ReceiveWrite(s:Server, s':Server, p:Packet, sp:seq<Packet>)
        requires p.msg.Message_Write?
        requires ServerValid(s)
        requires PacketValid(p)
    {
        var new_vc := AdvanceVC(s.gvc, s.id);
        var meta := Meta(p.msg.key_write, new_vc, p.msg.deps_write);
        var local := set m | m in p.msg.local.Values;
        var new_icache := s.icache[p.msg.key_write := s.icache[p.msg.key_write] + local + {meta}];
        var wreply := LPacket(s.id, p.src, Message_Write_Reply(p.msg.key_write, new_vc));
        var propagate := LPacket(s.id, s.next, Message_Propagation(p.msg.key_write, {meta}, s.id));
        && s' == s.(gvc:=new_vc, icache := new_icache)
        && sp == [wreply] + [propagate]
    }


    predicate ReceivePropagate(s:Server, s':Server, p:Packet, sp:seq<Packet>)
        requires p.msg.Message_Propagation?
        requires ServerValid(s)
        requires PacketValid(p)
    {
        if s.next == p.msg.start then
            var vcs := set x | x in p.msg.metas :: x.vc;
            var new_gvc := FoldVC(s.gvc, vcs);
            var deps := set x | x in p.msg.metas :: x.deps;
            var new_deps := FoldDependency(map[], deps);

            var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, new_deps);
            && s' == s.(gvc := new_gvc, icache := new_icache, ccache := new_ccache)
            && sp == []
        else 
            var new_icache := FoldMetaIntoICache(s.icache, p.msg.metas);
            && s' == s.(icache := new_icache)
            && sp == [LPacket(s.id, s.next, p.msg)]
    }


    /** Client */
    datatype Client = Client(
        id : int,
        local : map<Key, Meta>,
        deps : Dependency
    )

    predicate ClientValid(c:Client)
    {
        && Nodes <= c.id < Nodes + Clients
        && (forall k :: k in c.local ==> k in Keys_domain && MetaValid(c.local[k]) && c.local[k].key == k)
        && DependencyValid(c.deps)
    }

    predicate ClientInit(c:Client, id:int)
        requires Nodes <= id < Nodes + Clients
    {
        && c.id == id
        && c.local == map[]
        && c.deps == map[]
    }

    predicate SendRead(c:Client, c':Client, sp:seq<Packet>)
        requires ClientValid(c)
    {
        var k :| 0 <= k < MaxKeys as int;
        
        if k in c.local then 
            && c' == c
            && sp == []
        else 
            var server :| 0 <= server < Nodes as int;
            && c' == c
            && sp == [LPacket(c.id, server, Message_Read(k, c.deps))]
    }

    predicate ReceiveReadReply(c:Client, c':Client, p:Packet, sp:seq<Packet>)
        requires ClientValid(c)
        requires p.msg.Message_Read_Reply?
        requires PacketValid(p)
    {
        var m := Meta(p.msg.key_rreply, p.msg.vc_rreply, p.msg.deps_rreply);

        && c' == c.(local := c.local[p.msg.key_rreply := m], deps := DependencyInsertOrMerge(c.deps, p.msg.key_rreply, p.msg.vc_rreply))
        && sp == []
    }

    predicate SendWrite(c:Client, c':Client, sp:seq<Packet>)
        // requires ClientValid(c)
    {
        var k :| 0 <= k < MaxKeys as int;
        var server :| 0 <= server < Nodes as int;
        && c' == c
        && sp == [LPacket(c.id, server, Message_Write(k, c.deps, c.local))]
    }

    predicate ReceiveWriteReply(c:Client, c':Client, p:Packet, sp:seq<Packet>)
        requires p.msg.Message_Write_Reply?
    {
        var k := p.msg.key_wreply;
        var vc := p.msg.vc_wreply;

        var m := Meta(k, vc, c.deps);
        && c' == c.(local := c.local[k := m])
        && sp == []
    }

    function {:opaque} ExtractSentPacketsFromIos(ios:seq<CMIo>) : seq<Packet>
        ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios
    {
        if |ios| == 0 then
            []
        else if ios[0].LIoOpSend? then
            [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
        else
            ExtractSentPacketsFromIos(ios[1..])
    }

    predicate ServerProcessPacket(s:Server, s':Server, ios:seq<CMIo>)
        requires ServerValid(s)
        requires |ios| >= 1
        requires ios[0].LIoOpReceive?
        requires PacketValid(ios[0].r)
        requires var msg := ios[0].r.msg; 
                msg.Message_Read? || msg.Message_Write? || msg.Message_Propagation?
    {
        && (forall io :: io in ios[1..] ==> io.LIoOpSend?)
        && var sent_packets := ExtractSentPacketsFromIos(ios);
            match ios[0].r.msg 
                case Message_Read(_,_) => ReceiveRead(s, s', ios[0].r, sent_packets)
                case Message_Write(_,_,_) => ReceiveWrite(s, s', ios[0].r, sent_packets)
                case Message_Propagation(_,_,_) => ReceivePropagate(s, s', ios[0].r, sent_packets)
    }

    // predicate NextProcessPacket(s:Server, s':Server, c:Client, c':Client, ios:seq<CMIo>)
    //     requires ServerValid(s)
    //     requires ClientValid(c)
    // {
    //     && |ios| >= 1
    //     && if ios[0].LIoOpTimeoutReceive? then
    //         s' == s && |ios| == 1
    //         else
    //         (&& ios[0].LIoOpReceive?
    //         && if ios[0].r.msg.Message_Read? || ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation? then
    //             ServerProcessPacket(s, s', ios)
    //            else
    //             ClientProcessPacket(c, c', ios)
    //         )
    // }

    predicate ServerNextProcessPacket(s:Server, s':Server, ios:seq<CMIo>)
        requires ServerValid(s)
    {
        && |ios| >= 1
        && if ios[0].LIoOpTimeoutReceive? then
            s' == s && |ios| == 1
           else
            (&& ios[0].LIoOpReceive?
             && PacketValid(ios[0].r)
            && if ios[0].r.msg.Message_Read? || ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation? then
                ServerProcessPacket(s, s', ios)
               else
                s' == s && |ios| == 1
            )
    }

    datatype LServer = LServer(s:Server)

    predicate LServerInit(s:LServer, id:int)
        requires 0 <= id < Nodes
    {
        && ServerInit(s.s, id)
        // && s.nextActionIndex == 0
    }

    predicate LServerNext(s:LServer, s':LServer, ios:seq<CMIo>)
    {
        && ServerValid(s.s)
        && ServerNextProcessPacket(s.s, s'.s, ios)
    }


    predicate ClientProcessPacket(s:Client, s':Client, ios:seq<CMIo>)
        requires ClientValid(s)
        requires |ios| >= 1
        requires ios[0].LIoOpReceive?
        requires PacketValid(ios[0].r)
        requires var msg := ios[0].r.msg;
                msg.Message_Read_Reply? || msg.Message_Write_Reply?
    {
        && (forall io :: io in ios[1..] ==> io.LIoOpSend?)
        && var sent_packets := ExtractSentPacketsFromIos(ios);
            match ios[0].r.msg 
                case Message_Read_Reply(_,_,_) => ReceiveReadReply(s, s', ios[0].r, sent_packets)
                case Message_Write_Reply(_,_) => ReceiveWriteReply(s, s', ios[0].r, sent_packets)
    }

    predicate ClientNextProcessPacket(s:Client, s':Client, ios:seq<CMIo>)
        requires ClientValid(s)
    {
        && |ios| >= 1
        && if ios[0].LIoOpTimeoutReceive? then
            s' == s && |ios| == 1
           else
            (&& ios[0].LIoOpReceive?
            && PacketValid(ios[0].r)
            && if ios[0].r.msg.Message_Read_Reply? || ios[0].r.msg.Message_Write_Reply? then
                ClientProcessPacket(s, s', ios)
               else
                s' == s && |ios| == 1
            )
    }

    predicate SpontaneousIos(ios:seq<CMIo>, clocks:int)
        requires 0<=clocks<=1
    {
        && clocks <= |ios|
        && (forall i :: 0<=i<clocks ==> ios[i].LIoOpReadClock?)
        && (forall i :: clocks<=i<|ios| ==> ios[i].LIoOpSend?)
    }

    predicate ClientNoReceiveNext(s:Client, s':Client, nextActionIndex:int, ios:seq<CMIo>)
        requires ClientValid(s)
    {
        var sent_packets := ExtractSentPacketsFromIos(ios);

        if nextActionIndex == 1 then 
            && SpontaneousIos(ios, 0)
            && SendRead(s, s', sent_packets)
        else 
            && nextActionIndex == 3
            && SpontaneousIos(ios, 0)
            && SendWrite(s, s', sent_packets)
    }

    datatype LClient = LClient(c:Client, nextActionIndex:int)

    predicate LClientInit(s:LClient, id:int)
        requires Nodes <= id < Nodes + Clients
    {
        && ClientInit(s.c, id)
        && s.nextActionIndex == 0
    }

    predicate LClientNext(s:LClient, s':LClient, ios:seq<CMIo>)
    {
        && ClientValid(s.c)
        && s'.nextActionIndex == (s.nextActionIndex + 1) % 3
        && if s.nextActionIndex == 0 then 
            ClientNextProcessPacket(s.c, s'.c, ios)
           else 
            ClientNoReceiveNext(s.c, s'.c, s.nextActionIndex, ios)
    }

}