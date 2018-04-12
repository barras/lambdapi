(** Term representation.

    This module defines the main abstract syntax tree representation for terms
    (including types), which relies on the {!module:Bindlib} library. A set of
    functions are also provided for basic term manipulations. *)

open Extra
open Files

(** {6 Term and rewriting rules representation} *)

(** Representation of a term (or type). *)
type term =
  | Vari of term Bindlib.var
  (** Free variable. *)
  | Type
  (** "Type" constant. *)
  | Kind
  (** "Kind" constant. *)
  | Symb of sym
  (** Symbol (static or definable). *)
  | Prod of term * (term, term) Bindlib.binder
  (** Dependent product. *)
  | Abst of term * (term, term) Bindlib.binder
  (** Abstraction. *)
  | Appl of term * term
  (** Application. *)
  | Meta of meta * term array
  (** Metavariable with its environment. *)
  | Patt of int option * string * term array
  (** Pattern variable (used in the LHS of rewriting rules). *)
  | TEnv of term_env * term array
  (** Term environment (used in the RHS of rewriting rules). *)

(** The {!const:Patt(i,s,ar)} constructor represents a pattern variable, which
    may only appear in the LHS (left hand side or pattern) of rewriting rules.
    It is identified by a {!type:string} name [s] (unique in a rewriting rule)
    and it carries an environment [ar] that should contain a set of (distinct)
    free variables (i.e., terms of the form {!const:Vari(x)}). They correspond
    to the only free variables that may appear in a matched term. Note that we
    must use the type {!type:term array} so that the variable may be bound. In
    particular, the type {!type:tvar array} would not be suitable. The element
    [i] (of type {!type:int option}) gives the index (if any) of the slot that
    is reserved for the matched term in the environment of the RHS (right hand
    side or action) of the rewriting rule. When [i] is {!const:None}, then the
    variable is not bound in the RHS. When it is {!const:Some(i)}, then either
    it is bound in the RHS, or it appears non-linearly in the LHS.

    The {!const:TEnv(te,ar)} constructor corresponds to a form of metavariable
    [te], with an associated environment [ar]. When it is used in the RHS of a
    rewriting rule, the metavariable [te] must be bound. When a rewriting rule
    applies, the metavariables that are bound in the RHS are substituted using
    an environment that was constructed during the matching of the LHS. *)

(** Representation of a constant or function symbol. *)
 and sym =
  { sym_name  : string        (** Name of the symbol. *)
  ; sym_type  : term ref      (** Type of the symbol. *)
  ; sym_path  : module_path   (** Module in which it is defined.  *)
  ; sym_rules : rule list ref (** Rewriting rules for the symbol. *)
  ; sym_const : bool          (** Tells whether it is constant.   *) }

(** The {!recfield:sym_type} field contains a reference for a technical reason
    related to the representation of signatures as binary files (see functions
    {!val:Sign.link} and {!val:Sign.unlink}). This is necessary to ensure that
    two identical symbols are always physically equal, even across signatures.
    It should not be mutated for any other reason.

    The rewriting rules associated to a symbol are stored in the symbol itself
    (in the {!recfield:sym_rules}). Note that a symbol should not be given any
    reduction rule if it is marked as constant (i.e., if {!recfield:sym_const}
    has value [true]). *)

(** Representation of a rewriting rule. *)
 and rule =
  { lhs   : term list                        (** Left  hand side.  *)
  ; rhs   : (term_env, term) Bindlib.mbinder (** Right hand side.  *)
  ; arity : int (** Required number of arguments to be applicable. *) }

(** A rewriting rule is formed of a LHS (left hand side), which is the pattern
    that should be matched for the rule to apply, and a RHS (right hand side),
    which gives the action to perform if the rule applies.

    The LHS (or pattern) of a rewriting rule is always formed of a head symbol
    (on which the rule is defined) applied to a list of arguments. The list of
    arguments is given in {!recfield:lhs}, but the head symbol itself does not
    need to be stored since the rules are always carried by symbols. *)

 and term_env =
  | TE_Vari of term_env Bindlib.var
  | TE_Some of (term, term) Bindlib.mbinder
  | TE_None

(* NOTE to check if rule [r] applies to term [t] using our representation, one
   should first substitute the [r.lhs] binder (using [Bindlib.msubst]) with an
   array of pattern variables [args] (which size should match the arity of the
   binder), thus obtaining a term list [lhs]. Then, to check if [r] applies to
   term [t] (which head must be the definable symbol corresponding to [r]) one
   should test  equality (with unification) between [lhs] and the arguments of
   [t]. If they are not equal then the rule does not match. Otherwise, [t] may
   be rewritten to the term obtained by substituting [r.rhs] with [args] (note
   that its pattern variables should have been substituted at this point. *)

(** Representation of a metavariable. *)
 and meta =
  { meta_name  : meta_name
  ; meta_type  : term
  ; meta_arity : int
  ; meta_value : (term, term) Bindlib.mbinder option ref }

 and meta_name =
   | Defined  of string
   | Internal of int

let internal (m:meta) : bool =
  match m.meta_name with
  | Defined _ -> false
  | Internal _ -> true

(* NOTE a metavariable is represented using a multiple binder. It can hence be
   instanciated with an open term,  provided that its which free variables are
   in the environment.  The values for the free variables are provided  by the
   second argument of the [Meta] constructor,  which can be used to substitute
   the binder whenever the metavariable has been instanciated. *)

(** Representation of a rule specification, used for checking SR. *)
type rspec =
  { rspec_symbol : sym                  (** Head symbol of the rule.    *)
  ; rspec_ty_map : (string * term) list (** Type for pattern variables. *)
  ; rspec_rule   : rule                 (** The rule itself.            *) }

(** Free {!type:term} variable. *)
type tvar = term Bindlib.var

type tbinder = (term, term) Bindlib.binder

(** Injection of [Bindlib] variables into terms. *)
let mkfree : tvar -> term = fun x -> Vari(x)

(** Injection of [Bindlib] variables into term place-holders. *)
let te_mkfree : term_env Bindlib.var -> term_env = fun x -> TE_Vari(x)

(** [unfold t] unfolds the toplevel metavariable in [t]. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Meta(m,e)            ->
      begin
        match !(m.meta_value) with
        | None    -> t
        | Some(b) -> unfold (Bindlib.msubst b e)
      end
  | TEnv(TE_Some(f), ar) -> unfold (Bindlib.msubst f ar)
  | _                    -> t

(******************************************************************************)
(* Boxed terms *)

(** Short name for boxed terms. *)
type tbox = term Bindlib.bindbox

(** [_Vari x] injects the free variable [x] into the bindbox so that it may be
    available for binding. *)
let _Vari : tvar -> tbox = Bindlib.box_of_var

(** [_Type] injects the constructor [Type] in the [bindbox] type. *)
let _Type : tbox = Bindlib.box Type

(** [_Kind] injects the constructor [Kind] in the [bindbox] type. *)
let _Kind : tbox = Bindlib.box Kind

(** [_Symb s] injects the constructor [Symb(s)] in the [bindbox] type. *)
let _Symb : sym -> tbox = fun s -> Bindlib.box (Symb(s))

(** [_Appl t u] lifts the application of [t] and [u] to the [bindbox] type. *)
let _Appl : tbox -> tbox -> tbox = fun t u ->
  Bindlib.box_apply2 (fun t u -> Appl(t,u)) t u

(** [_Prod a x f] lifts a dependent product node to the [bindbox] type given a
    boxed term [a] (the type of the domain), a prefered name [x] for the bound
    variable, and a function [f] to build the [binder] (codomain). *)
let _Prod : tbox -> string -> (tvar -> tbox) -> tbox = fun a x f ->
  let b = Bindlib.vbind mkfree x f in
  Bindlib.box_apply2 (fun a b -> Prod(a,b)) a b

let _Prod_bv : tbox -> tvar -> tbox -> tbox = fun a x b ->
  Bindlib.box_apply2 (fun a b -> Prod(a,b)) a (Bindlib.bind_var x b)

(** [_Abst a x f] lifts an abstraction node to the [bindbox] type given a term
    [a] (the type of the bound variable),  the prefered name [x] for the bound
    variable, and the function [f] to build the [binder] (body). *)
let _Abst : tbox -> string -> (tvar -> tbox) -> tbox = fun a x f ->
  let b = Bindlib.vbind mkfree x f in
  Bindlib.box_apply2 (fun a b -> Abst(a,b)) a b

(** [_Meta u ar] lifts a metavariable [u] to the [bindbox] type, given
    its environment [ar]. The metavariable should not  be instanciated
    when calling this function. *)
let _Meta : meta -> tbox array -> tbox = fun u ar ->
  Bindlib.box_apply (fun ar -> Meta(u,ar)) (Bindlib.box_array ar)

let _Patt : int option -> string -> tbox array -> tbox = fun i n ar ->
  Bindlib.box_apply (fun ar -> Patt(i,n,ar)) (Bindlib.box_array ar)

let _TEnv : term_env Bindlib.bindbox -> tbox array -> tbox = fun te ar ->
  Bindlib.box_apply2 (fun te ar -> TEnv(te,ar)) te (Bindlib.box_array ar)

(** [lift t] lifts a [term] [t] to the [bindbox] type, thus gathering its free
    variables, making them available for binding. At the same time,  the names
    of the bound variables are automatically updated by [Bindlib]. *)
let rec lift : term -> tbox = fun t ->
  let lift_binder b x = lift (Bindlib.subst b (mkfree x)) in
  let lift_term_env te =
    match te with
    | TE_Vari(x) -> Bindlib.box_of_var x
    | TE_Some(_) -> assert false
    | TE_None    -> assert false
  in
  match unfold t with
  | Vari(x)     -> _Vari x
  | Type        -> _Type
  | Kind        -> _Kind
  | Symb(s)     -> _Symb s
  | Prod(a,b)   -> _Prod (lift a) (Bindlib.binder_name b) (lift_binder b)
  | Abst(a,t)   -> _Abst (lift a) (Bindlib.binder_name t) (lift_binder t)
  | Appl(t,u)   -> _Appl (lift t) (lift u)
  | Meta(r,m)   -> _Meta r (Array.map lift m)
  | Patt(i,n,m) -> _Patt i n (Array.map lift m)
  | TEnv(te,m)  -> _TEnv (lift_term_env te) (Array.map lift m)

(******************************************************************************)
(* Metavariables *)

(** [unset u] returns [true] if [u] is not instanciated. *)
let unset : meta -> bool = fun u -> !(u.meta_value) = None

(** [meta_name m] returns a parsable identifier for the meta-variable [m]. *)
let meta_name : meta -> string = fun m ->
  match m.meta_name with
  | Defined(s) -> Printf.sprintf "?%s" s
  | Internal(k) -> Printf.sprintf "?%i" k

(** Representation of the existing meta-variables. *)
type meta_map =
  { str_map   : meta StrMap.t
  ; int_map   : meta IntMap.t
  ; free_keys : Cofin.t }

(** [empty_meta_map] is an emptu meta-variable map. *)
let empty_meta_map : meta_map =
  { str_map   = StrMap.empty
  ; int_map   = IntMap.empty
  ; free_keys = Cofin.full }

(** [all_metas] is the reference in which the meta-variables are stored. *)
let all_metas : meta_map ref = ref empty_meta_map

(** [find_meta name] returns the meta-variable mapped to [name] in [all_metas]
    or raises [Not_found] if the name is not mapped. *)
let find_meta : meta_name -> meta = fun name ->
  match name with
  | Defined(s) -> StrMap.find s !all_metas.str_map
  | Internal(k) -> IntMap.find k  !all_metas.int_map

(** [exists_meta name] tells whether [name] is mapped in [all_metas]. *)
let exists_meta : meta_name -> bool = fun name ->
  match name with
  | Defined(s) -> StrMap.mem s !all_metas.str_map
  | Internal(k) -> IntMap.mem k  !all_metas.int_map

(** [add_meta s a n] creates a new user-defined meta-variable named [s], of
    type [a] and arity [n]. Note that [all_metas] is updated automatically
    at the same time. *)
let add_meta : string -> term -> int -> meta = fun s a n ->
  let m = { meta_name  = Defined(s)
          ; meta_type  = a
          ; meta_arity = n
          ; meta_value = ref None }
  in
  let str_map = StrMap.add s m !all_metas.str_map in
  all_metas := {!all_metas with str_map}; m

(** [new_meta a n] creates a new internal meta-variable of type [a] and arity
    [n]. Note that [all_metas] is updated automatically at the same time. *)
let new_meta : term -> int -> meta = fun a n ->
  let (k, free_keys) = Cofin.take_smallest !all_metas.free_keys in
  let m = { meta_name  = Internal(k)
          ; meta_type  = a
          ; meta_arity = n
          ; meta_value = ref None }
  in
  let int_map = IntMap.add k m !all_metas.int_map in
  all_metas := {!all_metas with int_map; free_keys}; m

(******************************************************************************)
(* Functions on terms *)

(** [get_args t] returns a tuple [(h, args)] where [h] if the head of the term
    and [args] is the list of its arguments. *)
let get_args : term -> term * term list = fun t ->
  let rec get_args acc t =
    match unfold t with
    | Appl(t,u) -> get_args (u::acc) t
    | t         -> (t, acc)
  in get_args [] t

(** [add_args h args] builds the application of a term [h] to a list [args] of
    of arguments. This function is the inverse of [get_args]. *)
let add_args : term -> term list -> term = fun t args ->
  let rec add_args t args =
    match args with
    | []      -> t
    | u::args -> add_args (Appl(t,u)) args
  in add_args t args

(** [eq t u] tests the equality of the two terms [t] and [u] (modulo
    alpha-equivalence). *)
let rec eq_list : (term * term) list -> unit = fun l ->
  match l with
  | [] -> ()
  | (a,b) :: l ->
     match unfold a, unfold b with
     | Vari(x1)   , Vari(x2) when Bindlib.eq_vars x1 x2 -> eq_list l
     | Type       , Type
     | Kind       , Kind        -> eq_list l
     | Symb(s1)   , Symb(s2) when s1 == s2 -> eq_list l
     | Prod(a1,b1), Prod(a2,b2)
     | Abst(a1,b1), Abst(a2,b2) ->
        let (_,b1,b2) = Bindlib.unbind2 mkfree b1 b2 in
        eq_list ((a1,a2)::(b1,b2)::l)
     | Appl(t1,u1), Appl(t2,u2) -> eq_list ((t1,t2)::(u1,u2)::l)
     | Patt(_,_,_), _
     | _          , Patt(_,_,_)
     | TEnv(_,_)  , _
     | _          , TEnv(_,_)   -> assert false
     | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
        let l = ref l in
        Array.iter2 (fun a b -> l := (a,b)::!l) a1 a2;
        eq_list !l
     | _          , _           -> raise Exit

let eq : term -> term -> bool = fun a b ->
  try eq_list [a,b]; true with Exit -> false

(** [distinct_vars a] checks that [a] is made of distinct variables. *)
let distinct_vars (a:term array) : bool =
  let acc = ref [] in
  let fn t =
    match t with
    | Vari v ->
       if List.exists (Bindlib.eq_vars v) !acc then raise Exit
       else acc := v::!acc
    | _ -> raise Exit
  in
  let res = try Array.iter fn a; true with Exit -> false in
  acc := []; res

(** [to_var t] returns [x] if [t = Vari x] and fails otherwise. *)
let to_var (t:term) : tvar = match t with Vari x -> x | _ -> assert false

(** [occurs u t] checks whether the metavariable [u] occurs in [t]. *)
(*REMOVE:let rec occurs : meta -> term -> bool = fun r t ->
  match unfold t with
  | Prod(a,b)
  | Abst(a,b)   -> occurs r a || occurs r (Bindlib.subst b Kind)
  | Appl(t,u)   -> occurs r t || occurs r u
  | Meta(u,e)   -> u == r || Array.exists (occurs r) e
  | Type
  | Kind
  | Vari(_)
  | Symb(_)     -> false
  | Patt(_,_,_)
  | TEnv(_,_)   -> assert false*)

(** [occurs m t] checks whether the metavariable [m] occurs in [t]. *)
let occurs (m:meta) (t:term) : bool =
  let rec occurs (t:term) : unit =
    match unfold t with
    | Patt(_,_,_) | TEnv(_,_) -> assert false
    | Vari(_) | Type | Kind | Symb(_) -> ()
    | Prod(a,f) | Abst(a,f) ->
       begin
         occurs a;
         let _,b = Bindlib.unbind mkfree f in
         occurs b
       end
    | Appl(a,b) -> occurs a; occurs b
    | Meta(m',ts) ->
       if m==m' then raise Exit else Array.iter occurs ts
  in
  try occurs t; false with Exit -> true

(******************************************************************************)
(* Representation of goals and proofs. *)

(** Representation of an environment for variables. *)
type env = (string * (tvar * tbox)) list

(** Representation of a goal. *)
type goal =
  { g_meta : meta
  ; g_hyps : env
  ; g_type : term }

(** Representation of a theorem. *)
type theorem =
  { t_proof : meta
  ; t_open_goals : goal list
  ; t_focus : goal }
