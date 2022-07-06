(*
    From 4.2.1: A Lamport timestamp is a pair (c, p) where
    p ∈ ReplicaID is the unique identifier of the
        replica on which the edit is made.
    c ∈ ℕ is a counter that is stored at each replica
        and incremented for every operation.
*)
type ID = { c: int; p: int }
(*
    From 4.1: The cursor can be interpreted as a path
    through the local replica state structure A_p.

    A cursor(<k_1,...,k_(n−1)>, k_n ) consists of a
    (possibly empty) vector of keys <k_1,...,k_(n−1)>, and a
    final key k_n which is always present. k_n can be thought
    of as the final element of the vector, with the distinction
    that it is not tagged with a datatype, whereas the elements
    of the vector are tagged with the datatype of the branch node
    being traversed, either mapT or listT.
*)
type Key =
    | Doc
    | Head
    | Tail
    | Str of string
    | ID of ID

type Tag =
    | MapT of Key
    | ListT of Key
    | RegT of Key
    static member getKey: Tag -> Key =
        function
        | MapT (k)
        | ListT (k)
        | RegT (k) -> k

type Cursor = Tag list * Key
(*
    From Fig. 7:
    VAL ::= n                   n ∈ Number
        | str                   str ∈ String
        | true | false | null
        | {} | []
*)
type Value =
    | N of int
    | Str of string
    | True
    | False
    | Null
    | EmptyMap
    | EmptyArr
(*
    From 4.2.2:
    op(
        (* Lamport timestamp that uniquely identifies the operation *)
        id: ℕ x ReplicaID,

        (*
            set of causal dependencies of the operation, i.e. any
            operation o_1 that had already been applied when o_2 was generated.
        *)
        deps: P(ℕ x ReplicaID),

        (* cursor describing the position in the document being modified *)
        cur: cursor(<k_1,...,k_(n-1)>, k_n),

        (* mutation that was requested at the specified position *)
        mut: insert(v) | delete | assign(v)     v : VAL
    )
*)
type Mutation =
    | Insert of Value
    | Delete
    | Assign of Value

type Operation =
    { id: ID
      deps: ID Set
      cur: Cursor
      mut: Mutation }

(*
    From Fig 7.
    VAR ::= x                   x ∈ VarString
    EXPR ::= doc
        | x                     x ∈ Var
        | EXPR.get(key)         key ∈ String
        | EXPR.idx(i)           i >= 0
        | EXPR.keys
        | EXPR.values
    CMD ::= let x = EXPR
        | EXPR := v             v ∈ Val
        | EXPR.insertAfter(v)   v ∈ Val
        | EXPR.delete           v ∈ Val
        | YIELD
        | CMD; CMD
*)
type Var = string

type Expr =
    | Doc
    | Var of Var
    | Get of Expr * string
    | Idx of Expr * uint
    | Keys of Expr
    | Values of Expr

type Cmd =
    | Let of Var * Expr
    | Assign of Expr * Value
    | InsertAfter of Expr * Value
    | Delete of Expr
    | Yield
    | Sequence of Cmd * Cmd

type Doc =
    | MapDoc of pres: Map<Key, ID Set> * children: Map<Tag, Doc>
    | ListDoc of pres: Map<Key, ID Set> * children: Map<Tag, Doc> * next: Map<Key, Key>
    | RegDoc of mvreg: Map<ID, Value>
    member doc.child k =
        match doc with
        | MapDoc (_, children)
        | ListDoc (_, children, _) -> children.TryFind k
        | _ -> None
    member doc.childDefault t =
        match doc.child t with
        | Some(ch) -> ch
        | _ ->
            match t with
            | MapT k -> MapDoc(Map.empty,Map.empty)
            | ListT k -> ListDoc(Map.empty,Map.empty,Map.empty)
            | RegT k -> RegDoc(Map.empty)
    member doc.withChild t child = 
        match doc with
        | MapDoc(pres, children) ->
            MapDoc(pres, children.Add(t,child))
        | ListDoc(pres, children, next) ->
            ListDoc(pres, children.Add(t,child), next)
        | _ -> doc

(* The state of a Replica *)
type Replica =
    { variables: Map<Var, Cursor>
      root: Doc
      replicaID: int
      ops: ID Set
      queue: Operation list } // counter (as optimization)
    member A_p.idx2_5 (ctx: Doc) (path, last) i =
        match ctx, path, i with
        (*

                   k_1 ∈ dom(ctx)    ctx(k_1), cursor(<k_2,...,k_(n-1)>,k_n).idx(i) => cursor(<k_2,...,k_(n-1)>,k'_n)
            Idx_2:----------------------------------------------------------------------------------------------------
                           ctx,cursor(<k_1,k_2,...,k_(n-1)>,k_n).idx(i) => cursor(<k_1,k_2,...,k_(n-1)>,k'_n)
        *)
        | _, (t1 :: t2_n), i ->
            match ctx.child t1 with
            | Some(d) -> A_p.idx2_5 d (t2_n, last) i
            | _ -> (path, last)
        (*
                                     i = 0
            Idx_5:------------------------------------------
                   ctx, cursor(<>,k).idx(i) => cursor(<>,k)
        *)
        | ListDoc (_), [], 0u -> ([], last)
        (*
                   i > 0 ∧ ctx(next(k)) = k' ∧ k' ≠ tail    ctx(pres(k')) ≠ {}    ctx, cursor(<>,k').idx(i-1) => ctx'
            Idx_3:----------------------------------------------------------------------------------------------------
                                                    ctx, cursor(<>,k).idx(i) => ctx'

                   i > 0 ∧ ctx(next(k)) = k' ∧ k' ≠ tail    ctx(pres(k')) = {}    ctx, cursor(<>,k').idx(i) => cur'
            Idx_4:--------------------------------------------------------------------------------------------------
                                                   ctx, cursor(<>,k).idx(i) => cur'
        *)
        | ListDoc (pres, _, next), [], i ->
            match next.TryFind last with
            | Some (k1p) when k1p <> Key.Tail ->
                let inext = if pres.[k1p].IsEmpty then i else i - 1u
                A_p.idx2_5 ctx ([], k1p) inext
            | _ -> (path, last)
        | _ -> (path, last)

    member A_p.eval: Expr -> Cursor =
        function
        (*
            Doc:-----------------------------
                 A_p, doc => cursor(<>, doc)
        *)
        | Doc -> ([], Key.Doc)
        (*
                   x ∈ dom(A_p)
            Var:------------------
                 A_p, x => A_p(x)
        *)
        | Var (x) ->
            match A_p.variables.TryFind x with
            | Some(c) -> c
            | _ -> ([], Key.Doc)
        (*
                 A_p, expr => cursor(<k_1,...,k_(n-1)>,k_n)         k_n ≠ head
            Get:---------------------------------------------------------------
                 A_p, expr.get(key) => cursor(<k_1,...,k_(n-1),mapT(k_n)>,key)
        *)
        | Get (x, key) ->
            let (path,last) = A_p.eval x
            if last <> Head then (path @ [ MapT last ], Key.Str key) else (path,last)
        (*
                   A_p, expr => cursor(<k_1,...,k_(n-1)>, k_n)    A_p, cursor(<k_1,...,k_(n-1),listT(k_n)>, head).idx(i) => cur'
            Idx_1:---------------------------------------------------------------------------------------------------------------
                                                              A_p, expr.idx(i) => cur'
        *)
        | Idx (x, i) ->
            let (path,last) = A_p.eval x
            A_p.idx2_5 A_p.root (path @ [ ListT last ], Head) i
        | _ -> ([], Key.Doc)

    member A_p.keys2_3 ctx (path, last) =
        match ctx, path with
        (*
                    k_1 ∈ dom(ctx)    ctx(k_1), cursor(<k_2,...,k_(n-1)>,k_n).keys => keys
            Keys_3:------------------------------------------------------------------------
                              ctx, cursor(<k_1,k_2,...,k_(n-1)>,k_n).keys => keys
        *)
        | MapDoc (_, children), (t1 :: t2_n)
        | ListDoc (_, children, _), (t1 :: t2_n) ->
            match children.TryFind t1 with
            | Some (child) -> A_p.keys2_3 child (t2_n, last)
            | _ -> Set.empty
        (*
            keys(ctx) = { k | mapT(k) ∈ dom(ctx) ∨ listT(k) ∈ dom(ctx) ∨ regT(k) ∈ dom(ctx) }

                    map = ctx(mapT(k))    keys = { k | k ∈ keys(map) ∧ map(pres(k)) ≠ {} }
            Keys_2:------------------------------------------------------------------------
                                        A_p, cursor(<>,k).keys => keys
        *)
        | MapDoc (_, children), []
        | ListDoc (_, children, _), [] ->
            match children.TryFind(MapT last) with
            | Some (MapDoc (pres, children)) ->
                children.Keys
                |> Seq.map Tag.getKey
                |> Seq.filter pres.ContainsKey
                |> Set.ofSeq
            | _ -> Set.empty
        | _ -> Set.empty
    (*
                A_p, expr => cur    A_p, cur.keys => keys
        Keys_1:-------------------------------------------
                          A_p, expr.keys => keys
    *)
    member A_p.keys expr =
        match A_p.eval expr with
        | Some (cur) -> A_p.keys2_3 A_p.root cur
        | _ -> Set.empty

    member A_p.values2_3 ctx (path, last) =
        match ctx, path with
        (*
                   k_1 ∈ dom(ctx)    ctx(k_1), cursor(<k_2,...,k_(n-1)>,k_n).values => val
            Val_3:-------------------------------------------------------------------------
                             ctx, cursor(<k_1,k_2,...,k_(n-1)>,k_n).values => val
        *)
        | MapDoc (_, children), (t1 :: t2_n)
        | ListDoc (_, children, _), (t1 :: t2_n) ->
            match children.TryFind t1 with
            | Some (child) -> A_p.values2_3 child (t2_n, last)
            | _ -> []
        (*
                   regT(k) ∈ dom(ctx)    val = range(ctx(regT(k)))
            Val_2:-------------------------------------------------
                           ctx, cursor(<>,k).values => val
        *)
        | MapDoc (_, children), []
        | ListDoc (_, children, _), [] ->
            match children.TryFind(RegT last) with
            | Some (RegDoc (mvreg)) -> mvreg.Values |> List.ofSeq
            | _ -> []
        | _ -> []
    (*
               A_p, expr => cur    A_p, cur.values => val
        Val_1:--------------------------------------------
                         A_p, expr.values => val
    *)
    member A_p.values expr =
        match A_p.eval expr with
        | Some (cur) -> A_p.values2_3 A_p.root cur
        | _ -> []
    
    member A_p.addId t id mut: Doc = failwith "unimplemented"

    member A_p.applyOp op (doc: Doc) =
        match op with
        | { cur = (t1 :: t2_n,last) } ->
            let child = doc.childDefault t1
            let childPrime = A_p.applyOp { op with cur = (t2_n,last) } child
            let ctxPrime = A_p.addId t1 op.id op.mut
            ctxPrime.withChild t1 childPrime
        | { cur = ([], last)} -> failwith ""

    member A_p.apply op =
        { A_p with root = A_p.applyOp op A_p.root; queue = A_p.queue @ [op]; ops = A_p.ops.Add op.id }

    member A_p.makeOp cur mut =
        let ctr =
            Set.fold (fun acc elem -> max acc elem.c) 0 A_p.ops

        A_p.apply
            { id = { c = ctr + 1; p = A_p.replicaID }
              deps = A_p.ops
              cur = cur
              mut = mut }

    member A_p.exec: Cmd -> Replica =
        function
        | Let (var, expr) ->
            match A_p.eval expr with
            | Some (cur) -> { A_p with variables = A_p.variables.Add(var, cur) }
            | _ -> A_p // TODO: show some error message?
        | Assign (expr, value) ->
            match A_p.eval expr with
            | Some (cur) -> A_p.makeOp cur (Mutation.Assign(value))
            | _ -> A_p
        | InsertAfter (expr, value) ->
            match A_p.eval expr with
            | Some (cur) -> A_p.makeOp cur (Mutation.Insert(value))
            | _ -> A_p
        | Delete (expr) ->
            match A_p.eval expr with
            | Some (cur) -> A_p.makeOp cur Mutation.Delete
            | _ -> A_p
        | Yield -> failwith "Not Implemented"
        | Sequence (cmd1, cmd2) ->
            let A_pPrime = A_p.exec cmd1
            A_pPrime.exec cmd2

// let r: Replica = {variables = Map.empty; root = RegDoc(Map.empty) }
// printfn "%A" (r.exec(Let("foo",Expr.Doc)))
