(** Evaluation and conversion. *)

open Lplib open Base open Extra
open Common open Error open Debug
open Term
open Print

(** The head-structure of a term t is:
- λx:_,h if t=λx:a,u and h is the head-structure of u
- Π if t=Πx:a,u
- h _ if t=uv and h is the head-structure of u
- ? if t=?M[t1,..,tn] (and ?M is not instantiated)
- t itself otherwise (TYPE, KIND, x, f)

A term t is in head-normal form (hnf) if its head-structure is invariant by
reduction.

A term t is in weak head-normal form (whnf) if it is an abstration or if it
is in hnf. In particular, a term in head-normal form is in weak head-normal
form.

A term t is in strong normal form (snf) if it cannot be reduced further.
*)

(** Logging function for whnf. *)
let log_whnf = Logger.make 'w' "whnf" "whnf"
let log_whnf = log_whnf.pp

(** Logging function for snf. *)
let log_snf = Logger.make 'e' "snf " "snf"
let log_snf = log_snf.pp

(** Logging function for conversion. *)
let log_conv = Logger.make 'c' "conv" "conversion"
let log_conv = log_conv.pp

(** Convert modulo eta. *)
let eta_equality : bool Timed.ref = Console.register_flag "eta_equality" false

(** Counter used to preserve physical equality in {!val:whnf}. *)
let steps : int Stdlib.ref = Stdlib.ref 0


let counter, reset =
  let l = Stdlib.ref [] in
  (fun () ->
    let r = Stdlib.ref 0 in
    l := r :: !l;
    r),
  (fun () -> List.iter (fun r -> r := 0) !l)

let ins = counter ()
let perm = counter ()
let ac = counter()
let tag = counter()
let ac_cut = counter()
let shr = counter()

let stat() =
  out Stdlib.(!Error.err_fmt)
    "shr: %d\ttag: %d \tcut: %d\tac: %d\tinsert: %d\tperm: %d\n"
    !shr !tag !ac_cut !ac !ins !perm;
  reset()

let _ = at_exit stat

(** {1 Simple term manipulations related to AC *)


let get_ac f t =
  let rec aliens acc ts =
    match ts with
    | [] -> List.rev acc
    | t::ts -> aux acc t ts
  and aux acc t ts =
    match get_args t with
    | Symb g, [u1;u2] when g == f -> aux acc u1 (u2::ts)
    | _ -> aliens (t::acc) ts in
  aux [] t []

(* Checks whether [t1] and [t2] are both AC expressions (over the same operation),
   assuming that both [t1] and [t2] are in whnf
   In case of success [ac] is called with both alien lists,
   otherwise [nonac] is called with both heads and arguments. 
*)
let get2_args_or_ac t1 t2 ~ac ~nonac =
  match get_args t1, get_args t2 with
  | (Symb f,[_;_]),(Symb g,[_;_]) when f==g && is_ac f -> ac f (get_ac f t1) (get_ac f t2)
  | (h1,stk1),(h2,stk2) -> nonac h1 stk1 h2 stk2
     


let ac_mv =
  { meta_key   = -1
  ; meta_type  = Timed.ref Kind
  ; meta_arity = 1
  ; meta_value = let x = new_var "ac" in Timed.ref (Some(bind_mvar [|x|] (Vari x))) }

let tag_ac t = incr tag; Meta(ac_mv,[|t|])

(*let term_tag t =
  match t with
  | Bvar _ -> "Bvar"
  | Vari _ -> "Vari"
  | Type -> "TYPE"
  | Kind -> "KIND"
  | Symb _ -> "Symb"
  | Prod _ -> "Prod"
  | Abst _ -> "Abst"
  | Appl _ -> "Appl"
  | Meta _ -> "Meta"
  | Patt _ -> "Patt"
  | Plac _ -> "Plac"
  | Wild -> "Wild"
  | TRef _ -> "TRef"
  | LLet _ -> "LLet"
 *)
let rec is_ac_whnf t =
  match t with
  | Meta(m,_) when m == ac_mv -> true
  | Meta(m, ts) ->
      begin
        match Timed.(!(m.meta_value)) with
        | None    -> false
        | Some(b) -> is_ac_whnf (msubst b ts)
      end
  | TRef(r) ->
      begin
        match Timed.(!r) with
        | None    -> false
        | Some(v) -> is_ac_whnf v
      end
  | _ -> false

let term =
  let v = ac_mv.meta_value in
  fun ppf t ->
  let bd = Timed.(!v) in
  let b = Timed.(!print_meta_args) in
  Timed.(print_meta_args := true);
  Timed.(v := None);
  Print.term ppf t;
  Timed.(print_meta_args := b);
  Timed.(v := bd)


(** [app2 s t1 t2] builds the application of [s] to [t1] and [t2]. *)
let app2 s t1 t2 = Appl(Appl(Symb s, t1), t2)
let app2_ac s t1 t2 = tag_ac(Appl(Appl(Symb s, t1), t2))



(** [left_comb (+) [t1;t2;t3]] generates [((t1+t2)+t3)]. *)
let left_comb s =
  let rec comb acc ts =
    match ts with
    | [] -> acc
    | t::ts -> comb (app2_ac s acc t) ts
  in
  function
  | [] | [_] -> assert false
  | t::ts -> comb t ts

(** [right_comb (+) [t1;t2;t3]] generates [(t1+(t2+t3))]. *)
let right_comb s =
  let rec comb ts acc =
    match ts with
    | [] -> acc
    | t::ts -> comb ts (app2_ac s t acc)
  in
  fun ts ->
  match List.rev ts with
  | [] | [_] -> assert false
  | t::ts -> comb ts t

(** [comb s norm ts] computes the [norm]-form of the comb obtained by applying
    [s] to [ts]. *)
let comb s =
  match s.sym_prop with
  | AC Left -> left_comb s
  | AC Right -> right_comb s
  | _ -> assert false



(** {1 Define reduction functions parametrised by {!whnf}} *)

(** [hnf whnf t] computes a hnf of [t] using [whnf]. *)
let hnf : (term -> term) -> (term -> term) = fun whnf ->
  let rec hnf t =
    match whnf t with
    | Abst(a,t) -> Abst(a, let x,t = unbind t in bind_var x (hnf t))
    | t -> t
  in hnf

(** [snf whnf t] computes a snf of [t] using [whnf]. *)
let snf : (term -> term) -> (term -> term) = fun whnf ->
  let rec snf t =
    if Logger.log_enabled() then log_snf "snf %a" term t;
    let t = whnf t in
    if Logger.log_enabled() then log_snf "whnf = %a" term t;
    match t with
    | Vari _
    | Type
    | Kind
    | Symb _
    | Plac _ (* may happen when reducing coercions *)
      -> t
    | LLet(_,t,b) -> snf (subst b t)
    | Prod(a,b) ->
      Prod(snf a, let x,b = unbind b in bind_var x (snf b))
    | Abst(a,b) ->
      Abst(snf a, let x,b = unbind b in bind_var x (snf b))
    | Appl(t,u)   -> Appl(snf t, snf u)
    | Meta(m,ts)  -> Meta(m, Array.map snf ts)
    | Patt(i,n,ts) -> Patt(i,n,Array.map snf ts)
    | Bvar _      -> assert false
    | Wild        -> assert false
    | TRef _      -> assert false
  in snf

(** [eq_modulo norm a b] tests the convertibility of [a] and [b] by comparing
    their [norm] forms. *)
let eq_modulo : (term -> term) -> term eq = fun norm ->
  let rec eq : (term * term) list -> unit = fun l ->
    match l with
    | [] -> ()
    | (a,b)::l ->
    if Logger.log_enabled () then
      log_conv "eq_modulo %a ≡ %a %a"
        term a term b (D.list (D.pair term term)) l;
    (* We first check equality modulo alpha. *)
    if LibTerm.eq_alpha a b then eq l else
    (* FIXME? Instead of computing the norm of each side right away, we could
       perhaps do it more incrementally (the reduction of beta-redexes, let's
       and local definitions as done in whnf could be integrated here) and,
       when both heads are function symbols, use an heuristic like in Matita
       to decide which side to unfold first. *)
    let a = norm a and b = norm b in
    if Logger.log_enabled () then
      log_conv "eq_modulo after norm %a ≡ %a" term a term b;
    get2_args_or_ac a b
      (* AC case *)
      ~ac:(fun _f al bl ->
        if List.length al <> List.length bl then raise Exit;
        (* Here, we could avoid re-reducing the terms of al and bl *)
        eq (List.rev_append2 al bl l))
      ~nonac:(fun a astk b bstk ->
        (* Non-AC case *)
    if List.length astk <> List.length bstk then raise Exit;
    let l = List.rev_append2 astk bstk l in
    match a, b with
    | Patt(None,_,_), _ | _, Patt(None,_,_) -> assert false
    | Patt(Some i,_,ts), Patt(Some j,_,us) ->
      if i=j then eq (List.add_array2 ts us l) else raise Exit
    | Kind, Kind
    | Type, Type -> eq l
    | Vari x, Vari y when eq_vars x y -> eq l
    | Symb f, Symb g when f == g -> eq l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = unbind2 b1 b2 in eq ((a1,a2)::(b1,b2)::l)
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when Timed.(!eta_equality) ->
      let x,b = unbind b in eq ((b, Appl(t, Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | Bvar _, _ | _, Bvar _ -> assert false
    | Appl _, _ | _, Appl _ -> assert false
    | _ -> raise Exit)
  in
  fun a b ->
  try eq [(a,b)]; true
  with Exit -> if Logger.log_enabled () then log_conv "failed"; false

(** Reduction permissions. *)
type rw_tag = [ `NoRw | `NoExpand ]

(** Configuration of the reduction engine. *)
type config =
  { varmap : term VarMap.t (** Variable definitions. *)
  ; rewrite : bool (** Whether to apply user-defined rewriting rules. *)
  ; expand_defs : bool (** Whether to expand definitions. *)
  ; dtree : sym -> dtree (** Retrieves the dtree of a symbol *) }

(** [make ?dtree ?rewrite c] creates a new configuration with tags [?rewrite]
    (being empty if not provided), context [c] and dtree map [?dtree]
    (defaulting to getting the dtree from the symbol). By default, beta
    reduction and rewriting is enabled for all symbols. *)
let make : ?dtree:(sym -> dtree) -> ?tags:rw_tag list -> ctxt -> config =
  fun ?(dtree=fun sym -> Timed.(!(sym.sym_dtree))) ?(tags=[]) context ->
  let expand_defs = not @@ List.mem `NoExpand tags in
  let rewrite = not @@ List.mem `NoRw tags in
  {varmap = Ctxt.to_map context; rewrite; expand_defs; dtree}

(** Abstract machine stack. *)
type stack = term list
(*type ac_stack = (sym option * term) list*)

(** [to_tref t] transforms {!constructor:Appl} into
   {!constructor:TRef}. *)
(* BB: create a ref for LLet? *)
let to_tref : term -> term = fun t ->
  match t with
  | TRef _ -> t
  | Appl _ -> TRef(Timed.ref(Some t))
  | Symb s when s.sym_prop <> Const -> TRef(Timed.ref(Some t))
  | t when is_ac_whnf t -> TRef(Timed.ref(Some t))
  | t -> t

(** {1 Define the main {!whnf} function that takes a {!config} as argument} *)
let depth = Stdlib.ref 0

let deep f x = incr depth; let v = f x in decr depth; v
let incr_depth f = incr depth; let v = f() in decr depth; v

let _sym_aco f =
  match f.sym_prop with
  | AC _ -> Some f
  | _ -> None

let is_sym_aco f aco =
  match aco with
  | Some g when f==g -> true
  | _ -> false

(** [tree_walk norm dt stk] tries to apply a rewrite rule by matching the
    stack [stk] against the decision tree [dt], possibly reducing stack
    elements with [norm]. The resulting state of the abstract machine is
    returned in case of success. Even if matching fails, the stack [stk] may
    be imperatively updated since a reduction step taken in elements of the
    stack is preserved (this is done using {!constructor:Term.term.TRef}). *)
let tree_walk : (sym option -> term -> term) -> dtree -> stack -> (term * stack) option =
  fun norm tree stk ->
  if Logger.log_enabled () then
    log_whnf "%atree_walk %a" D.depth !depth (D.list term) stk;
  let (lazy capacity, lazy tree) = tree in
  let vars = Array.make capacity Kind in (* dummy terms *)
  let bound = Array.make capacity None in
  (* [walk tree stk cursor vars_id id_vars] where [stk] is the stack of terms
     to match and [cursor] the cursor indicating where to write in the [vars]
     array described in {!module:Term} as the environment of the RHS during
     matching. [vars_id] maps the free variables contained in the term to the
     indexes defined during tree build, and [id_vars] is the inverse mapping
     of [vars_id]. *)
  let rec walk tree stk cursor vars_id id_vars =
    let open Tree_type in
    match tree with
    | Fail -> None
    | Leaf(rhs_subst, r) -> (* Apply the RHS substitution *)
        (* Allocate an environment where to place terms coming from the
           pattern variables for the action. *)
        assert (List.length rhs_subst = r.vars_nb);
        let env_len = r.vars_nb + r.xvars_nb in
        let env = Array.make env_len None in
        (* Retrieve terms needed in the action from the [vars] array. *)
        let f (pos, (slot, xs)) =
          match bound.(pos) with
          | Some(_) -> env.(slot) <- bound.(pos)
          | None    ->
                let xs = Array.map (fun e -> IntMap.find e id_vars) xs in
                env.(slot) <- Some(bind_mvar xs vars.(pos))
        in
        List.iter f rhs_subst;
        (* Complete the array with fresh meta-variables if needed. *)
        for i = r.vars_nb to env_len - 1 do
          env.(i) <- Some(bind_mvar [||] (Plac false))
        done;
        Some (subst_patt env r.rhs, stk)
    | Cond({ok; cond; fail})                              ->
        let next =
          match cond with
          | CondNL(i, j) ->
              if incr_depth (fun () -> (*log_whnf"start NL";*)let r=eq_modulo (norm None) vars.(i) vars.(j) in (*log_whnf"end NL";*) r)
              then ok else fail
          | CondFV(i,xs) ->
              let allowed =
                (* Variables that are allowed in the term. *)
                let fn id =
                  try IntMap.find id id_vars with Not_found -> assert false
                in
                Array.map fn xs
              in
              let forbidden =
                (* Term variables forbidden in the term. *)
                IntMap.filter (fun id _ -> not (Array.mem id xs)) id_vars
              in
              (* Ensure there are no variables from [forbidden] in [b]. *)
              let no_forbidden b =
                not (IntMap.exists (fun _ x -> occur_mbinder x b)
                       forbidden)
              in
              (* We first attempt to match [vars.(i)] directly. *)
              let b = bind_mvar allowed vars.(i) in
              if no_forbidden b
              then (bound.(i) <- Some b; ok) else
              (* As a last resort we try matching the SNF. *)
              let b = bind_mvar allowed (snf (norm None) vars.(i)) in
              if no_forbidden b
              then (bound.(i) <- Some b; ok)
              else fail
        in
        walk next stk cursor vars_id id_vars
    | Eos(l, r)                                                    ->
        let next = if stk = [] then l else r in
        walk next stk cursor vars_id id_vars
    | Node({swap; children; store; abstraction; default; product}) ->
        match List.destruct stk swap with
        | exception Not_found     -> None
        | (left, examined, right) ->
        if TCMap.is_empty children && abstraction = None && product = None
        (* If there is no specialisation tree, try directly default case. *)
        then
          let fn t =
            let cursor =
              if store then (vars.(cursor) <- examined; cursor + 1)
              else cursor
            in
            let stk = List.reconstruct left [] right in
            walk t stk cursor vars_id id_vars
          in
          Option.bind default fn
        else
          let s = Stdlib.(!steps) in
(*          let _ = log_whnf "Node start reduce" in*)
          let (t, args) = incr_depth (fun () -> get_args (norm None examined)) in
(*          let _ = log_whnf "Node end reduce" in*)
          let args = if store then List.map to_tref args else args in
          (* If some reduction has been performed by [norm] ([steps <>
             0]), update the value of [examined] which may be stored into
             [vars]. *)
          if Stdlib.(!steps) <> s then
            begin
              match examined with
              | TRef(v) -> incr shr; log_whnf "update"; Timed.(v := Some(add_args t args))
              | _       -> ()
            end;
          let cursor =
            if store then (vars.(cursor) <- add_args t args; cursor + 1)
            else cursor
          in
          (* [default ()] carries on the matching on the default branch of the
             tree. Nothing is added to the stack. *)
          let default () =
            let fn d =
              let stk = List.reconstruct left [] right in
              walk d stk cursor vars_id id_vars
            in
            Option.bind default fn
          in
          (* [walk_binder a  b  id tr]  matches  on  binder  [b]  of type  [a]
             introducing variable  [id] and branching  on tree [tr].  The type
             [a] and [b] substituted are re-inserted in the stack.*)
          let walk_binder a b id tr =
            let (bound, body) = unbind b in
            let vars_id = VarMap.add bound id vars_id in
            let id_vars = IntMap.add id bound id_vars in
            let stk = List.reconstruct left (a::body::args) right in
            walk tr stk cursor vars_id id_vars
          in
          match t with
          | Type       ->
              begin
                try
                  let matched = TCMap.find TC.Type children in
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Symb(s)    ->
              let cons = TC.Symb(s.sym_path, s.sym_name, List.length args) in
              begin
                try
                  (* Get the next sub-tree. *)
                  let matched = TCMap.find cons children in
                  (* Re-insert the arguments the symbol is applied to in the
                     stack. *)
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Vari(x)    ->
              begin
                try
                  let id = VarMap.find x vars_id in
                  let matched = TCMap.find (TC.Vari(id)) children in
                  (* Re-insert the arguments the variable is applied to in the
                     stack. *)
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Abst(a, b) ->
              begin
                match abstraction with
                | None        -> default ()
                | Some(id,tr) -> walk_binder a b id tr
              end
          | Prod(a, b) ->
              begin
                match product with
                | None        -> default ()
                | Some(id,tr) -> walk_binder a b id tr
              end
          | Kind
          | Patt _
          | Meta(_, _) -> default ()
          | Plac _     -> assert false
             (* Should not appear in typechecked terms. *)
          | TRef(_)    -> assert false (* Should be reduced by [norm]. *)
          | Appl(_)    -> assert false (* Should be reduced by [norm]. *)
          | LLet(_)    -> assert false (* Should be reduced by [norm]. *)
          | Bvar _     -> assert false
          | Wild       -> assert false (* Should not appear in terms. *)
  in
  walk tree stk 0 VarMap.empty IntMap.empty

(** {b NOTE} that in {!val:tree_walk} matching with trees involves two
    collections of terms.
    1. The argument stack [stk] of type {!type:stack} which contains the terms
       that are matched against the decision tree.
    2. An array [vars] containing subterms of the argument stack [stk] that
       are filtered by a pattern variable. These terms may be used for
       non-linearity or free-variable checks, or may be bound in the RHS.

    The [bound] array is similar to the [vars] array except that it is used to
    save terms with free variables. *)

(** {b NOTE} in the {!val:tree_walk} function, bound variables involve three
    elements:
    1. a {!constructor:Term.term.Abst} which introduces the bound variable in
       the term;
    2. a {!constructor:Term.term.Vari} which is the bound variable previously
       introduced;
    3. a {!constructor:Tree_type.TC.t.Vari} which is a simplified
       representation of a variable for trees. *)


(** {1 A total order on terms.}
    It is stable by reduction because it compares normal forms.
    However it is not stable by instantiation (of Meta) and mutation (TRef).
    For efficiency reasons it proceeds like the conversion test:
    the normal form is computed lazily, by performing weak head
    reduction and comparing heads. If heads have the same constructor
    proceed recursively on subterms (left to right lexico order). If
    they differ, they are ordered according to the constructor tag.

    Note: bound variables are greater than free variable. Hence, in
      [λx. λy. f(x,y,z)], we have [z<x<y] because [x] becomes free before [y].

    Currently, it is not antisymmetric (Meta and Patt cases). This should not be
    an issue since we cannot match against those constructors. *)

(** First a little library of comparison functions with effect *)

type 'a effect_comparison_function = 'a -> 'a -> int * 'a *  'a

(* Case when [f] has no effect on its input *)
let fpure f a b = (f a b, a, b)

let _lexf f1 f2 c (a1,a2) (b1,b2) =
  let cmp1,a1',b1' = f1 a1 b1 in
  if cmp1 <> 0 then (cmp1, c a1' a2, c b1' b2)
  else
    let cmp2,a2',b2' = f2 a2 b2 in
    (cmp2, c a1' a2', c b1' b2')

let _lex3f f1 f2 f3 c (a1,a2,a3) (b1,b2,b3) =
  let cmp1,a1',b1' = f1 a1 b1 in
  if cmp1 <> 0 then (cmp1, c a1' a2 a3, c b1' b2 b3)
  else
    let cmp2,a2',b2' = f2 a2 b2 in
    if cmp2 <> 0 then (cmp2, c a1' a2' a3, c b1' b2' b3)
    else
      let cmp3,a3',b3' = f3 a3 b3 in
      (cmp3, c a1' a2' a3', c b1' b2' b3')

(* Same as [lexf] but avoids using [mk] when [f1] and [f2] have no effect. 
   It Assumes [c a1 a2] is equal to [a] and [c b1 b2] is equal to [b]. *)
let sharing_lexf f1 f2 mk a b =
  fun (a1,a2) (b1,b2) ->
  let cmp1,a1',b1' = f1 a1 b1 in
  if cmp1 <> 0 then
    let a' = if a1==a1' then a else mk a1' a2 in
    let b' = if b1==b1' then b else mk b1' b2 in
    (cmp1, a', b')
  else
    let cmp2,a2',b2' = f2 a2 b2 in
    let a' = if a1==a1' && a2==a2' then a else mk a1' a2' in
    let b' = if b1==b1' && b2==b2' then b else mk b1' b2' in
    (cmp2, a', b')

let sharing_lex3f f1 f2 f3 mk a b =
  fun (a1,a2,a3) (b1,b2,b3) ->
  let cmp1,a1',b1' = f1 a1 b1 in
  if cmp1 <> 0 then
    let a' = if a1==a1' then a else mk a1' a2 a3 in
    let b' = if b1==b1' then b else mk b1' b2 b3 in
    (cmp1, a', b')
  else
    let cmp2,a2',b2' = f2 a2 b2 in
    if cmp2 <> 0 then
      let a' = if a1==a1' && a2==a2' then a else mk a1' a2' a3 in
      let b' = if b1==b1' && b2==b2' then b else mk b1' b2' b3 in
      (cmp2, a', b')
    else
      let cmp3,a3',b3' = f3 a3 b3 in
      let a' = if a1==a1' && a2==a2' && a3==a3' then a else mk a1' a2' a3' in
      let b' = if b1==b1' && b2==b2' && b3==b3' then b else mk b1' b2' b3' in
      (cmp3, a', b')

(* Left to right lexicogrpahic order on list, assuming
   lists of same length *)
let rec flist f al bl =
  match al,bl with
    | a::al', b::bl' ->
       sharing_lexf f (flist f) (fun x l -> x::l) al bl (a,al') (b,bl')
    | [], [] -> (0,[],[])
    | _ -> assert false


(* t1 and t2 are aliens in whnf *)
let norm_cmp norm : term effect_comparison_function =
  let rec cmp t1 t2 = cmp_nf (norm t1) (norm t2)
  and cmp_nf t1 t2 =
    get2_args_or_ac t1 t2
      ~ac:(fun f l1 l2 ->
        sharing_lexf (fpure Stdlib.compare) (flist cmp_nf) (fun _ l -> comb f l)
          t1 t2 (List.length l1,l1) (List.length l2,l2))
      ~nonac:(fun h1 stk1 h2 stk2 ->
        (* 3-way lexico: first compare # of arguments, then the head, and
           the arguments (left to right) *)
        sharing_lex3f (fpure Stdlib.compare) cmp_head (flist cmp) (fun _ h stk -> add_args h stk)
          t1 t2 (List.length stk1, h1,stk1) (List.length stk2, h2, stk2))
  and cmp_head t1 t2 =
  match unfold t1, unfold t2 with
  | Vari x, Vari x' -> (compare_vars x x',t1,t2)
  | Type, Type
  | Kind, Kind
  | Wild, Wild -> (0,t1,t2)
  | Symb s, Symb s' -> Sym.compare s s', t1,t2
  | Prod(t,u), Prod(t',u') ->
     sharing_lexf cmp cmp_binder (fun t u->Prod(t,u)) t1 t2 (t,u) (t',u')
  | Abst(t,u), Abst(t',u') ->
     sharing_lexf cmp cmp_binder (fun t u->Abst(t,u)) t1 t2 (t,u) (t',u')
  | LLet(a,t,u), LLet(a',t',u') ->
     sharing_lex3f cmp cmp cmp_binder (fun a t u->LLet(a,t,u)) t1 t2 (a,t,u) (a',t',u')
  (* Non antisymmetric cases (Meta and Patt could be improved): *)
  | Meta(m,_ts), Meta(m',_ts') -> (Meta.compare m m', t1, t2)
  | Patt(i,_,_), Patt(i',_,_) -> (Stdlib.compare i i', t1, t2)
  | TRef _, TRef _ -> (0, t1, t2)
  (* Absurd cases *)
  | Appl _, _ | _, Appl _ -> assert false
  | Bvar _, _ | _, Bvar _ -> assert false
  (* Diagonal cases *)
  | t, t' -> (cmp_tag t t', t, t')
  and cmp_binder b1 b2 =
    (* [x] is always greater than the variables in [b1] and [b2],
       so the order does not depend on the choice of [x]. *)
    let (x,t1,t2) = unbind2 b1 b2 in
    let (c,t1',t2') = cmp t1 t2 in
    (c, bind_var x t1', bind_var x t2')
  in cmp_nf

(** {1 AC normaliaation} *)

let rec merge2 norm ord al bl acc =
  match al,bl with
  | [], _ -> List.rev_append acc bl
  | _, [] -> List.rev_append acc al
  | a::al, b::bl ->
     incr perm;
     let (c,a',b') = norm a b in
     if ord c then merge2 norm ord (a'::al) bl (b'::acc)
     else merge2 norm ord al (b'::bl) (a'::acc)
(* Merge sort... *)
let rec merge_step norm ord ll acc =
  match ll with
  | [] -> acc
  | [l] -> l::acc
  | l1::l2::ll ->  incr ins; merge_step norm ord ll (merge2 norm ord l1 l2 []::acc)

let rec is_sorted norm ord all =
  match all with
  | [] | [_] -> true
  | al1::((a2::_)::_ as all) ->
     (match List.rev al1 with
     | a1::_ ->
        (*log_whnf "MERGE CMP: %a >? %a" term a1 term a2;*)
        let (c,_,_) = norm a1 a2 in
        if ord c then false else is_sorted norm ord all
     | [] -> assert false)
  | _::[]::_ -> assert false

let rec merge norm ord ll =
  match ll with 
  | [] -> []
  | [l] -> l
  | _ -> merge norm ord (merge_step norm ord ll [])
let merge norm ord al =
  let all = List.map (fun (wh,f,a) -> if wh then get_ac f a else [a]) al in
  if is_sorted norm ord all then
    (log_whnf "MERGE: already sorted %a" (D.list (D.list term)) all;
     List.flatten all)
  else
    (log_whnf "MERGE: %a" (D.list (D.list term)) all;
     merge norm ord all)

let insert norm ord t =
  incr ins;
  let rec aux ts =
    match ts with
    | [] -> [t]
    | t1::ts ->
       let (c,t,t1) = norm t t1 in
       if ord c then
         (* If [t] is not inserted in head position, then commutativity (and assoc) is used *)
         (incr perm; Stdlib.incr steps; t1::aux ts)
       else t::t1::ts in
  aux

(* Insertion sort *)
let _sort_aliens norm al =
  List.fold_left
    (fun sortd t -> insert (norm_cmp norm) (fun c -> c>0) t sortd)
    [] (List.rev al)

(* merge sort *)
let sort_aliens norm al =
  merge (norm_cmp norm) (fun c -> c>0) al


(* Determines whether [t] reduces to [f t1 t2] and call [ac], otherwise
   call [nonac] with the reduced form of [t].
   /!\ It is essential to match t before trying to reduce [t], otherwise exponential behavior
   The idea is that destructing an AC term in whnf should be linear.

   Alternatively, we may require that [norm] performs no AC in head position.
   This would be even better, e.g. for f(t1,a) when a reduces to f(t2,t3)
   we could avoid sorting [t2;t3], then [t1;t2;t3] *)
let dest_ac norm f t ~ac ~nonac =
(*  match get_args t with
  | Symb g, [t1;t2] when f==g -> ac t1 t2
  | _ ->*)
     let t = norm t in
     (match get_args t with
     | Symb g, [t1;t2] when f==g ->
        if is_ac_whnf t then nonac true t
        else ac t1 t2
     | _ -> nonac false t) 


(* /!\ right subterms [rts] (out spine) in regular order
   [racc] aliens in rverse order *)
let left_aliens norm f t1 t2 =
  let rec proc out_spine t1 rts racc =
    dest_ac norm f t1
      ~ac:(fun t11 t12 ->
        if out_spine then Stdlib.incr steps;
        proc out_spine t11 (t12::rts) racc)
      ~nonac:(fun wh t1' ->
        let racc' = (wh,f,t1')::racc in
        (match rts with
          [] -> List.rev racc'
        | t2::rts -> proc true t2 rts racc'))
  in proc false t1 [t2] []

(* /!\ left subterms [rlts] in reverse order
   [acc] aliens in regular order *)
let right_aliens norm f t1 t2 =
  let rec proc out_spine rlts t2 acc =
    dest_ac norm f t2
      ~ac:(fun t21 t22 ->
        if out_spine then Stdlib.incr steps;
        proc out_spine (t21::rlts) t22 acc)
    ~nonac:(fun wh t2' ->
      let acc' = (wh,f,t2')::acc in
      (match rlts with
        [] -> acc'
      | t1::rlts -> proc true rlts t1 acc'))
  in proc false [t1] t2 []

let aliens norm f t1 t2 =
  match f.sym_prop with
  | AC Left -> left_aliens norm f t1 t2
  | AC Right -> right_aliens norm f t1 t2
  | _ -> assert false



(** [ac norm t] computes a head-AC [norm] form. *)
let ac aco norm t =
  match get_args t, aco with
  | (Symb f, [_;_]), Some g when f==g -> t
  | (Symb f, [t1;t2]), _ ->
     begin match f.sym_prop with
     | AC _ ->
        incr ac;
        if Logger.log_enabled () then log_whnf "AC<- %a" term (app2 f t1 t2);
        let al = aliens (norm (Some f)) f t1 t2 in
        if Logger.log_enabled () then log_whnf "AC aliens: %a = %a" term (app2 f t1 t2) (D.list (D.pair D.bool term)) (List.map (fun (wh,_,t)->wh,t) al);
        let al = sort_aliens (norm None) al in
        if Logger.log_enabled () then log_whnf "AC-> %a => %a" term (app2 f t1 t2) (D.list term) al;
        comb f al
     | Commu ->
        let (c,t1,t2) = norm_cmp (norm None) (norm None t1) (norm None t2) in
        if c>0 then begin (* swap t1 and t2 *)
            Stdlib.incr steps; app2 f t2 t1
          end
        else t
     | _ -> t
     end
  | _ -> t

(** [whnf cfg t] computes a whnf of the term [t] wrt configuration [cfg]. *)
let whnf : config -> term -> term = fun cfg ->
  (* [whnf t] computes a whnf of [t]. *)
  let rec whnf aco t =
    let n = Stdlib.(!steps) in
    let u, stk = whnf_stk aco t [] in
    if Stdlib.(!steps) <> n then add_args u stk else unfold t

  (* [whnf_stk t stk] computes a whnf of [add_args t stk]. *)
  and whnf_stk : sym option -> term -> stack -> term * stack = fun aco t stk ->
    if Logger.log_enabled () then
      log_whnf "%awhnf_stk %a %a %a" D.depth !depth (D.option sym) aco term t (D.list term) stk;
    let t =
      if is_ac_whnf t then (log_whnf "%aAC whnf: %a" D.depth !depth term t;incr ac_cut; t)
      else ac aco (deep whnf) t in
    match unfold t with
    | Appl(f,u) -> whnf_stk aco f (to_tref u::stk)
    (*| _ ->
      if Logger.log_enabled() then
      log_whnf "%awhnf_stk %a %a" D.depth !depth term t (D.list term) stk;
      match t, stk with*)
    | Abst(_,f) ->
        begin
          match stk with
          | u::stk -> Stdlib.incr steps; whnf_stk aco (subst f u) stk
          | _ -> t, stk
        end
    | LLet(_,t,u) ->
        (*FIXME? instead of doing a substitution now, add a local definition
          instead to postpone the substitution when it will be necessary. But
          the following makes tests/OK/725.lp fail: *)
        (*let x,u = unbind u in
          whnf_stk {cfg with varmap = VarMap.add x t cfg.varmap} u stk*)
        Stdlib.incr steps; whnf_stk aco (subst u t) stk
    | Symb f when is_sym_aco f aco -> t, stk
    | Symb s ->
        begin match Timed.(!(s.sym_def)) with
        (* The invariant that defined symbols are subject to no
           rewriting rules is false during indexing for websearch;
           that's the reason for the when in the next line *)
        | Some u when Tree_type.is_empty (cfg.dtree s) ->
            if Timed.(!(s.sym_opaq)) || not cfg.expand_defs then t, stk
            else (Stdlib.incr steps; whnf_stk aco u stk)
        | None when not cfg.rewrite -> t, stk
        | _ ->
           begin match tree_walk whnf (cfg.dtree s) stk with
           | None -> log_whnf "%ano rule applies" D.depth !depth; t, stk
           | Some (t, rstk) ->
              if Logger.log_enabled () then
                log_whnf "%aapply rewrite rule (lhs stack %a)" D.depth !depth (D.list term) stk;
              Stdlib.incr steps; whnf_stk aco t rstk
           end
        end
    | Vari x ->
        begin match VarMap.find_opt x cfg.varmap with
        | Some v -> Stdlib.incr steps; whnf_stk aco v stk
        | None -> t, stk
        end
    | _ -> t, stk
  in fun t ->
     log_whnf "Start top whnf %a" term t;
     let t' = whnf None t in
     log_whnf "End top whnf %a" term t';
     t'

(** {1 Define exposed functions}
    that take optional arguments rather than a config. *)

type reducer = ?tags:rw_tag list -> ctxt -> term -> term

let time_reducer (f: reducer): reducer =
  let open Stdlib in let r = ref Kind in fun ?tags cfg t ->
    Debug.(record_time Rewriting (fun () -> r := f ?tags cfg t)); !r

(** [snf ~dtree c t] computes a snf of [t], unfolding the variables defined in
    the context [c]. The function [dtree] maps symbols to dtrees. *)
let snf : ?dtree:(sym -> dtree) -> reducer = fun ?dtree ?tags c t ->
  Stdlib.(steps := 0);
  let u = snf (whnf (make ?dtree ?tags c)) t in
  stat();
  if Stdlib.(!steps = 0) then unfold t else u

let snf ?dtree = time_reducer (snf ?dtree)

(** [hnf c t] computes a hnf of [t], unfolding the variables defined in the
    context [c], and using user-defined rewrite rules. *)
let hnf : reducer = fun ?tags c t ->
  Stdlib.(steps := 0);
  let u = hnf (whnf (make ?tags c)) t in
  if Stdlib.(!steps = 0) then unfold t else u

let hnf = time_reducer hnf

(** [eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c]. WARNING: may have side effects in TRef's introduced by whnf. *)
let eq_modulo : ?tags:rw_tag list -> ctxt -> term -> term -> bool =
  fun ?tags c -> eq_modulo (whnf (make ?tags c))

let eq_modulo =
  let open Stdlib in let r = ref false in fun ?tags c t u ->
  Debug.(record_time Rewriting (fun () -> r := eq_modulo ?tags c t u)); !r

(** [pure_eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c] with no side effects. *)
let pure_eq_modulo : ?tags:rw_tag list -> ctxt -> term -> term -> bool =
  fun ?tags c a b ->
  Timed.pure_test
    (fun (c,a,b) ->
      ((*Logger.set_debug_in "ce" false (fun () ->*) eq_modulo ?tags c a b))
    (c,a,b)

(** [whnf c t] computes a whnf of [t], unfolding the variables defined in the
   context [c], and using user-defined rewrite rules if [~rewrite]. *)
let whnf : reducer = fun ?tags c t ->
  Stdlib.(steps := 0);
  let u = whnf (make ?tags c) t in
  if Stdlib.(!steps = 0) then unfold t else u

let whnf = time_reducer whnf

(** [beta_simplify c t] computes a beta whnf of [t] in context [c] belonging
    to the set S such that (1) terms of S are in beta whnf normal format, (2)
    if [t] is a product, then both its domain and codomain are in S. *)
let beta_simplify : ctxt -> term -> term = fun c ->
  let tags = [`NoRw; `NoExpand] in
  let rec simp t =
    match get_args (whnf ~tags c t) with
    | Prod(a,b), _ ->
       let x, b = unbind b in
       Prod (simp a, bind_var x (simp b))
    | h, ts -> add_args_map h (whnf ~tags c) ts
  in simp

let beta_simplify =
  let open Stdlib in let r = ref Kind in fun c t ->
  Debug.(record_time Rewriting (fun () -> r := beta_simplify c t)); !r

(** If [s] is a non-opaque symbol having a definition, [unfold_sym s t]
   replaces in [t] all the occurrences of [s] by its definition. *)
let unfold_sym : sym -> term -> term =
  let unfold_sym : sym -> (term list -> term) -> term -> term =
    fun s unfold_sym_app ->
    let rec unfold_sym t =
      let h, args = get_args t in
      let args = List.map unfold_sym args in
      match h with
      | Symb s' when s' == s -> unfold_sym_app args
      | _ ->
          let h =
            match h with
            | Abst(a,b) -> Abst(unfold_sym a, unfold_sym_binder b)
            | Prod(a,b) -> Prod(unfold_sym a, unfold_sym_binder b)
            | Meta(m,ts) -> Meta(m, Array.map unfold_sym ts)
            | LLet(a,t,u) ->
                LLet(unfold_sym a, unfold_sym t, unfold_sym_binder u)
            | _ -> h
          in add_args h args
    and unfold_sym_binder b =
      let x, b = unbind b in bind_var x (unfold_sym b)
    in unfold_sym
  in
  fun s ->
  if Timed.(!(s.sym_opaq)) then fun t -> t else
  match Timed.(!(s.sym_def)) with
  | Some d -> unfold_sym s (add_args d)
  | None ->
  match Timed.(!(s.sym_rules)) with
  | [] -> fun t -> t
  | _ ->
      let unfold_sym_app args =
        match tree_walk (fun _ -> whnf []) Timed.(!(s.sym_dtree)) args with
        | Some(r,ts) -> add_args r ts
        | None -> add_args (Symb s) args
      in unfold_sym s unfold_sym_app

(** Dedukti evaluation strategies. *)
type strategy =
  | WHNF (** Reduce to weak head-normal form. *)
  | HNF  (** Reduce to head-normal form. *)
  | SNF  (** Reduce to strong normal form. *)
  | NONE (** Do nothing. *)

type strat =
  { strategy : strategy   (** Evaluation strategy. *)
  ; steps    : int option (** Max number of steps if given. *) }

(** [eval s c t] evaluates the term [t] in the context [c] according to
    strategy [s]. *)
let eval : strat -> ctxt -> term -> term = fun s c t ->
  match s.strategy, s.steps with
  | _, Some 0
  | NONE, _ -> t
  | WHNF, None -> whnf c t
  | SNF, None -> snf c t
  | HNF, None -> hnf c t
  (* TODO implement the rest. *)
  | _, Some _ -> wrn None "Number of steps not supported."; t
