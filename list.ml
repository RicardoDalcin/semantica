(* 
  Trabalho Final - Semântica Formal N - INF05516
                    2022/2

            Bernardo Beneduzi Borba
            Ricardo Hermes Dalcin

  Gramática Linguagem L1: 

  e ∈ Expr

  e ::= n | b | e1 op e2 | if e1 then e2 else e3
  | x | e1 e2 | fn x : T ⇒ e | let x : T = e1 in e2
  | let rec f : T1 → T2 = fn x : T1 ⇒ e1 in e2
  | (e1, e2) | fst e | snd e
  | nil : T | e1::e2 | hd e | tl e
  | match e1 with nil ⇒ e2 | x::xs ⇒ e3
  | just e | nothing : T
  | match e1 with nothing ⇒ e2 | just x ⇒ e3

  op ∈ {+, −, ∗, div, <, ≤, >, ≥, =, and, or}

  T ::= int | bool | T1 → T2 | T list | T1 ∗ T2 | maybe T
*)

type var = string

(* Tipos da linguagem L1 *)
type typeL1 =
    Int
  | Bool
  | TyFun of typeL1 * typeL1
  | TyList of typeL1
  | TyPair of typeL1 * typeL1
  | TyMaybe of typeL1
    
(* Conjunto op *)
type operator =
    OpPlus
  | OpMinus
  | OpTimes
  | OpDiv
  | OpGreater
  | OpGorE
  | OpEqual 
  | OpLorE
  | OpLess 
  | OpAnd
  | OpOr

(* Possíveis expressões da linguagem L1 *)
type expr =
    ExBool of bool
  | ExNumber of int
  | ExIf of expr * expr * expr
  | ExVar of var
  | ExOperation of operator * expr * expr
  | ExApplication of expr * expr
  | ExFunction of var * typeL1 * expr
  | ExLet of var * typeL1 * expr * expr
  | ExLetRec of var * typeL1 * typeL1 * var * typeL1 * expr * expr
  | ExPair of expr * expr
  | ExFst of expr
  | ExSnd of expr
  | ExNil of typeL1
  | ExList of expr * expr
  | ExHd of expr
  | ExTl of expr
  | ExMatchL of expr * expr * var * var * expr
  | ExJust of expr
  | ExNothing of typeL1
  | ExMatchM of expr * expr * var * expr

(* Valores da linguagem L1 *)
type value =
  | VNumber of int
  | VBool of bool
  | VList of value * value
  | VNil of typeL1
  | VPair of value * value
  | VClosure of var * typeL1 * expr * context
  | VRecClosure of var * typeL1 * typeL1 * var * typeL1 * expr * expr * context
  | VJust of value
  | VNothing of typeL1
and
  context = (string * value) list

(* Função que compara se dois tipos são iguais *)
let rec compareType ty1 ty2 = match (ty1,ty2) with
  | TyList a, TyList b when a = b -> true
  | TyList a, TyList b when a<>b -> compareType a b
  | (a, b) when a=b -> true
  | _ -> false
;;

(* Função que verifica a tipagem de uma dada expressão em determinado contexto gamma *)
let rec typeCheck (e:expr) gamma =
  match e with
  | ExNil (ty)                    -> Some (TyList ty)
  | ExNumber  (_)                 -> Some Int
  | ExBool (_)                    -> Some Bool
  | ExIf (e1,e2,e3)               ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      let ty3 = typeCheck e3 gamma in
      (match (ty1,ty2,ty3) with
       | (Some Bool, Some ty4, Some ty5) ->
           if (compareType ty4 ty5) 
           then Some ty5 
           else None
       | (_,_,_) -> None)
  | ExVar (x)                     ->
      (try
         Some (List.assoc x gamma)
       with Not_found ->
         None)
  | ExApplication (e1,e2)         ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some (TyFun (ty3,ty4)), Some ty5) -> 
           if (compareType ty3 ty5) 
           then Some ty4
           else None
       | _ -> None)
  | ExFunction (x,fTy,e1)         ->
      let ty1 = typeCheck e1 ((x, fTy)::gamma) in
      let t = (match ty1 with
          | Some t' -> Some (TyFun (fTy,t'))
          | _ -> None
        ) in
      t
  | ExList (e1,e2)                ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some (TyList ty4)) -> 
           if compareType ty3 ty4 
           then Some (TyList ty3) 
           else None
       | (_,_) -> None)
  | ExHd (e1)                     ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some (TyList ty2)) -> Some ty2
       | _ -> None)
  | ExTl (ExList(e1,e2))          ->
      let (ty1) = (typeCheck e2 gamma) in
      (match (ty1) with
       | (Some (TyList ty2)) -> ty1
       | _ -> None)
  | ExTl (e1)                     ->
      let (ty1) = (typeCheck e1 gamma) in
      (match (ty1) with
       | (Some (TyList ty2)) -> ty1
       | _ -> None)
  | ExOperation (OpPlus,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Int
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpMinus,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Int
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpTimes,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Int
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpDiv,e1,e2)     ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Int
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpGreater,e1,e2) ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpGorE,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpEqual,e1,e2)   ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else if ty3 = Bool && ty4 = Bool then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpLorE,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpLess,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpAnd,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Bool && ty4 = Bool then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpOr,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Bool && ty4 = Bool then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExLet (x,tyF,e1,e2)   ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 ((x, tyF)::gamma) in
      let t = (match (ty1,ty2) with
          | (Some ty3, Some ty4) -> 
              if compareType ty3 tyF 
              then Some ty4 
              else None
          | _ -> None) in
      t
  | ExLetRec (x, tyInF, tyOutF, y, ty1, e1, e2) 
    when compareType tyInF ty1  ->
      let gamma1 = (x, (TyFun (tyInF,tyOutF)))::gamma in
      let ty2 = typeCheck e2 gamma1 in
      let ty1 = typeCheck e1 ((y, ty1)::gamma1) in
      let t = (match (ty1,ty2) with
          | (Some ty3, Some ty4) when compareType ty3 tyOutF -> Some ty4
          | (Some ty3, Some ty4) -> None
          | _ -> None) in
      t
  | ExPair (e1, e2)               ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) -> Some (TyPair (ty3, ty4))
       | (None,_) -> None
       | (_,None) -> None)
  | ExFst (e1)                    ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some (TyPair (ty2, ty3))) -> Some ty2
       | _ -> None)
  | ExSnd (e1)                    ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some (TyPair (ty2, ty3))) -> Some ty3
       | _ -> None)
  | ExJust (e1)                   ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some ty1) -> Some (TyMaybe ty1) 
       | None -> None)
  | ExNothing (ty)                -> Some (TyMaybe ty)
  | ExMatchL (e1, e2, x, xs, e3)  ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some TyList tyL) -> 
           let ty2 = typeCheck e2 gamma in
           let gamma1 = (x, tyL)::gamma in
           let gamma2 = (xs, TyList tyL)::gamma1 in
           let ty3 = typeCheck e3 gamma2 in
           (match (ty2, ty3) with
            | (Some ty4, Some ty5) ->
                if (compareType ty4 ty5) 
                then Some ty5 
                else None
            | (_,_) -> None)
       | _ -> None
      )
  | ExMatchM (e1, e2, x, e3)  ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some TyMaybe tyM) -> 
           let ty2 = typeCheck e2 gamma in
           let ty3 = typeCheck e3 ((x, tyM)::gamma) in
           (match (ty2, ty3) with
            | (Some ty4, Some ty5) ->
                if (compareType ty4 ty5) 
                then Some ty5 
                else None
            | (_,_) -> None)
       | _ -> None
      )
  | _                             -> None
;;

(* Exceções tratadas pelo avaliador Big-Step *)
exception NoRuleApplies of string
exception DivisionByZero of string
exception EmptyListNotAllowed of string

(* Avaliador Big-Step para linguagem L1 *)
let rec eval (e: expr) gamma = 
  match e with
  | ExNumber (n) -> VNumber (n)
  | ExBool (b) -> VBool (b)
  | ExIf (e1,e2,e3) ->
      let v1 = eval e1 gamma in
      (match v1 with
       | VBool (true) -> eval e2 gamma
       | VBool (false) -> eval e3 gamma
       | _ -> raise (NoRuleApplies "Eval error: if"))
  | ExVar (x) ->
      let rec search (x: string) (gamma: (string * value) list) = 
        (match gamma with
         | [] -> raise (NoRuleApplies ("Eval error: var " ^ x))
         | (y,v)::tl -> if x = y then v else search x tl)
      in
      search x gamma
  | ExOperation (op, e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      (match (v1,v2) with
       | (VNumber (n1), VNumber (n2)) ->
           (match op with
            | OpPlus -> VNumber (n1 + n2)
            | OpMinus -> VNumber (n1 - n2)
            | OpTimes -> VNumber (n1 * n2)
            | OpDiv ->
                (match n2 with
                 | 0 -> raise (DivisionByZero "Eval error: div - division by zero is not allowed")
                 | _ -> VNumber (n1 / n2))
            | OpGreater -> VBool (n1 > n2)
            | OpGorE -> VBool (n1 >= n2)
            | OpEqual -> VBool (n1 = n2)
            | OpLorE -> VBool (n1 <= n2)
            | OpLess -> VBool (n1 < n2)
            | _ -> raise (NoRuleApplies "Eval error: operation"))
       | (VBool (b1), VBool (b2)) ->
           (match op with
            | OpAnd -> VBool (b1 && b2)
            | OpOr -> VBool (b1 || b2)
            | OpEqual -> VBool (b1 = b2)
            | _ -> raise (NoRuleApplies "Eval error: operation"))
       | _ -> raise (NoRuleApplies "Eval error: operation"))
  | ExApplication (e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      (match v1 with
       | VClosure (x, fTy, e1, gamma1) ->
           let gamma2 = (x, v2)::gamma1 in
           let v3 = eval e1 gamma2 in
           v3
       | VRecClosure (x, tyInF, tyOutF, y, ty1, e1, e2, gamma) ->
           let gamma1 = (x, v1)::gamma in
           let gamma2 = (y, v2)::gamma1 in
           let v3 = eval e1 gamma2 in
           v3
       | _ -> raise (NoRuleApplies "Eval error: application"))
  | ExFunction (x, fTy, e1) ->
      VClosure (x, fTy, e1, gamma)
  | ExLet (x, tyF, e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 ((x, v1)::gamma) in
      v2
  | ExLetRec (x, tyInF, tyOutF, y, ty1, e1, e2) ->
      let closure = VRecClosure (x, tyInF, tyOutF, y, ty1, e1, e2, gamma) in
      let v2 = eval e2 ((x, closure)::gamma) in
      v2
  | ExPair (e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      VPair (v1, v2)
  | ExFst (e) ->
      let v = eval e gamma in
      (match v with
       | VPair (v1, v2) -> v1
       | _ -> raise (NoRuleApplies "Eval error: fst"))
  | ExSnd (e) ->
      let v = eval e gamma in
      (match v with
       | VPair (v1, v2) -> v2
       | _ -> raise (NoRuleApplies "Eval error: snd"))
  | ExNil (ty) ->
      VNil (ty)
  | ExList (e1, e2) -> 
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      VList (v1, v2)
  | ExHd (e) ->
      let v = eval e gamma in
      (match v with
       | VNil (ty) -> raise (EmptyListNotAllowed "Eval error: hd - empty list")
       | VList (v1, v2) -> v1
       | _ -> raise (NoRuleApplies "Eval error: hd"))
  | ExTl (e) -> 
      let v = eval e gamma in
      (match v with
       | VNil (ty) -> raise (EmptyListNotAllowed "Eval error: hd - empty list")
       | VList (v1, v2) -> v2
       | _ -> raise (NoRuleApplies "Eval error: tl"))
  | ExMatchL (e1, e2, x, xs, e3) -> 
      let v1 = eval e1 gamma in
      (match v1 with
       | VNil (ty) -> eval e2 gamma
       | VList (v1, v2) ->
           let v3 = eval e3 ((x, v1)::(xs, v2)::gamma) in
           v3
       | _ -> raise (NoRuleApplies "Eval error: matchL"))
  | ExJust (e) ->
      let v = eval e gamma in
      VJust (v)
  | ExNothing (ty) ->
      VNothing (ty)
  | ExMatchM (e1, e2, x, e3) ->
      let v1 = eval e1 gamma in
      (match v1 with
       | VNothing (ty) -> eval e2 gamma
       | VJust (v1) ->
           let v2 = eval e3 ((x, v1)::gamma) in
           v2
       | _ -> raise (NoRuleApplies "Eval error: matchM"))
;;

(* Função que converte um tipo de L1 para uma string, com objetivo de tornar mais legível *)
let rec typeToString (ty: typeL1) : string =
  match ty with
  | Int  -> "int"
  | Bool -> "bool"
  | TyFun (tp1,tp2) -> "(" ^ (typeToString tp1) ^ " -> " ^ (typeToString tp2) ^ ")"
  | TyList a -> (typeToString a) ^ " list"
  | TyPair (tp1,tp2) -> "(" ^ (typeToString tp1) ^ " * " ^ (typeToString tp2) ^ ")"
  | TyMaybe a -> "maybe " ^ (typeToString a)
;;

(* Função que converte uma expressão de L1 para uma string, com objetivo de tornar mais legível *)
let rec exprToString (e: expr) : string =
  match e with
  | ExNumber (x) -> string_of_int x
  | ExBool (b) -> string_of_bool b
  | ExIf (e1,e2,e3) -> "(if " ^ (exprToString e1) ^ " then " ^ (exprToString e2) ^ " else " ^ (exprToString e3) ^ ")"
  | ExVar (x) -> x
  | ExOperation (op, e1, e2) -> 
      (match (op, e1, e2) with
       | (OpPlus, e3, e4) -> "(" ^ (exprToString e3) ^ " + " ^ (exprToString e4) ^ ")"
       | (OpMinus, e3, e4) -> "(" ^ (exprToString e3) ^ " - " ^ (exprToString e4) ^ ")"
       | (OpTimes, e3, e4) -> "(" ^ (exprToString e3) ^ " * " ^ (exprToString e4) ^ ")"
       | (OpDiv, e3, e4) -> "(" ^ (exprToString e3) ^ " div " ^ (exprToString e4) ^ ")"
       | (OpGreater, e3, e4) -> "(" ^ (exprToString e3) ^ " > " ^ (exprToString e4) ^ ")"
       | (OpGorE, e3, e4) -> "(" ^ (exprToString e3) ^ " >= " ^ (exprToString e4) ^ ")"
       | (OpEqual, e3, e4) -> "(" ^ (exprToString e3) ^ " = " ^ (exprToString e4) ^ ")"
       | (OpLorE, e3, e4) -> "(" ^ (exprToString e3) ^ " <= " ^ (exprToString e4) ^ ")"
       | (OpLess, e3, e4) -> "(" ^ (exprToString e3) ^ " < " ^ (exprToString e4) ^ ")"
       | (OpAnd, e3, e4) -> "(" ^ (exprToString e3) ^ " and " ^ (exprToString e4) ^ ")"
       | (OpOr, e3, e4) -> "(" ^ (exprToString e3) ^ " or " ^ (exprToString e4) ^ ")"
      )
  | ExApplication (e1, e2) -> "(" ^ (exprToString e1) ^ " " ^ (exprToString e2) ^ ")"
  | ExFunction (x, tyF, e1) -> "(fn " ^ x ^ ": " ^ (typeToString tyF) ^ " => " ^ (exprToString e1) ^ ")"
  | ExLet (x, tyF, e1, e2) -> "(let " ^ x ^ ": " ^ (typeToString tyF) ^ " = " ^ (exprToString e1) ^ " in " ^ (exprToString e2) ^ ")"
  | ExLetRec (x, tyInF, tyOutF, y, ty1, e1, e2) -> "(let rec " ^ x ^ ": " ^ (typeToString tyInF) ^ "->" ^ (typeToString tyOutF) ^ " = fn " ^ y ^ ": " ^ (typeToString ty1) ^ " => " ^ (exprToString e1) ^ " in " ^ (exprToString e2) ^ ")"
  | ExPair (e1, e2) -> "(" ^ (exprToString e1) ^ ", " ^ (exprToString e2) ^ ")"
  | ExFst (e1) -> "(fst " ^ (exprToString e1) ^ ")"
  | ExSnd (e1) -> "(snd " ^ (exprToString e1) ^ ")"
  | ExNil (ty) -> "(nil: " ^ (typeToString ty) ^ ")"
  | ExList (e1, e2) ->  (exprToString e1) ^ "::" ^ (exprToString e2)
  | ExHd (e1) -> "(hd " ^ (exprToString e1) ^ ")"
  | ExTl (e1) -> "(tl " ^ (exprToString e1) ^ ")"
  | ExMatchL (e1, e2, x, xs, e3) -> "(match " ^ (exprToString e1) ^ " with nil => " ^ (exprToString e2) ^ " | " ^ x ^ "::" ^ xs ^ " => " ^ (exprToString e3) ^ ")" 
  | ExJust (e1) -> "(just " ^ (exprToString e1) ^ ")"
  | ExNothing (ty) -> "(nothing: " ^ (typeToString ty) ^ ")"
  | ExMatchM (e1, e2, x, e3) -> "(match " ^ (exprToString e1) ^ " with nothing => " ^ (exprToString e2) ^ " | just " ^ x ^ " => " ^ (exprToString e3) ^ ")"
;;

(* Função que converte um contexto para uma string *)
let rec contextToString (c: context) : string =
  match c with
  | [] -> "]"
  | h :: t ->  ((fst h) ^ ": " ^ (valueToString (snd h)) ^ ", " ^ (contextToString t))
and
(* Função que converte um valor de L1 para uma string, com objetivo de tornar mais legível *)
  valueToString (v: value) : string =
  match v with
  | VNumber (x) -> string_of_int x
  | VBool (b) -> string_of_bool b
  | VNil (ty) -> "(nil: " ^ (typeToString ty) ^ ")"
  | VList (v1, v2) ->  (valueToString v1) ^ "::" ^ (valueToString v2)
  | VPair (v1, v2) -> "(" ^ (valueToString v1) ^ ", " ^ (valueToString v2) ^ ")"
  | VClosure (x, tyF, e1, c) -> "(fn " ^ x ^ ": " ^ (typeToString tyF) ^ " => " ^ (exprToString e1) ^ ") context = [" ^ (contextToString c)
  | VRecClosure (x, tyInF, tyOutF, y, ty1, e1, e2, c) -> "(let rec " ^ x ^ ": " ^ (typeToString tyInF) ^ "->" ^ (typeToString tyOutF) ^ " = fn " ^ y ^ ": " ^ (typeToString ty1) ^ " => " ^ (exprToString e1) ^ " in " ^ (exprToString e2) ^ ") context = [" ^ (contextToString c)
  | VJust (v1) -> "(just " ^ (valueToString v1) ^ ")"
  | VNothing (ty) -> "(nothing: " ^ (typeToString ty) ^ ")"
;;

(* Função que verifica se determinada expressão é bem tipada *)
let rec testWellTyped (e: expr) =
  let context = [] in
  let ty = typeCheck e context in
  (match (ty) with
   | (Some ty1) -> 
       (print_endline "Expressão bem tipada, com tipo:");
       (print_endline (typeToString ty1));
       true
   | None -> 
       (print_endline "Expressão mal tipada.");
       false
  )
;;

(* 
  Função usada para rodar os testes, verifica se a expressão é bem tipada e, se for, faz a sua avaliação 
  Printa na tela:
    - A expressão fornecida;
    - Se é bem tipada ou não;
    - Se for bem tipada:
      - O seu tipo;
      - O resultado da avaliação Big-Step.
*)
let rec runTest (e: expr) =
  (print_endline "-------------------------------");
  (print_endline "Expressão de entrada:");
  (print_endline (exprToString e));
  let wellTyped = testWellTyped e in
  if(wellTyped)
  then 
    let context = [] in
    let value = eval e context in
    (print_endline "Expressão de saída:");
    (print_endline (valueToString value));
    (print_endline "-------------------------------");
;;

(* Testes desenvolvidos *)
let test1 = ExNil Bool
let test2 = ExNumber 5
let test3 = ExBool true
let test4 = ExIf ((ExBool true), (ExNumber 5), (ExNumber 10)) 
let test5 = (ExFunction ("x", Int, (ExBool true)))
let test6 = ExApplication (test5, test2)
let test7 = ExList ((ExNumber 5), (ExList ((ExNumber 6), ExNil Int)))
let test8 = ExHd test7
let test9 = ExTl test7
let test10 = ExOperation (OpPlus, test2, test2)
let test11 = ExOperation (OpEqual, test2, test2)
let test12 = ExOperation (OpEqual, test3, test3)
let test13 = ExLet ("x", Int, test2, ExVar("x"))
let test14 = ExLet ("x", Int, test2, ExOperation (OpEqual, ExVar("x"), test2))
let test15 = ExLetRec("sum",
                      Int,Int,
                      "y",
                      Int,
                      ExIf(ExOperation (OpGorE, ExVar "y" , ExNumber 0),
                           ExOperation (OpPlus,(ExVar "y"), ExApplication(ExVar "sum", ExOperation(OpMinus,ExVar "y", ExNumber 1))),
                           ExNumber 0 ),
                      ExApplication(ExVar "sum", ExNumber 5));;
let test16 = ExPair (test2, test7)
let test17 = ExFst test16
let test18 = ExSnd test16
let test19 = ExLetRec (("soma"),
                       (TyList Int), Int, 
                       ("l"), 
                       (TyList Int), 
                       (ExMatchL ((ExVar "l"), 
                                  (ExNumber 0), 
                                  ("x"), 
                                  ("xs"), 
                                  ExOperation (OpPlus, 
                                               (ExVar "x"), 
                                               ExApplication ((ExVar "soma"), (ExVar "xs"))
                                              )
                                 )),
                       (ExApplication ((ExVar "soma"), test7))
                      )
let test20 = ExMatchM ((ExJust (ExNumber 5)), 
                       (ExBool false), 
                       "x", 
                       (ExOperation (OpEqual, 
                                     (ExVar "x"), 
                                     (ExNumber 5)
                                    )
                       )
                      )
    
let testIf = ExIf ((ExBool true), (ExNumber 5), (ExNumber 10))
let testOperation = ExOperation (OpPlus, (ExNumber 5), (ExNumber 10))
let testPair = ExPair (testIf, (ExNumber 10))
let testFst = ExFst testPair
let testSnd = ExSnd testPair
let testList = ExList ((ExNumber 5), (ExList ((ExNumber 6), ExNil Int)))
let testHd = ExHd testList
let testTl = ExTl testList
let testBoolOperation1 = ExOperation (OpAnd, ExBool true, ExBool false)
let testBoolOperation2 = ExOperation (OpOr, ExBool true, ExBool false)
let testBoolOperation3 = ExOperation (OpEqual, ExBool false, ExBool false)

(* Testes de expressões mal tipadas *)
let bad1 = ExIf ((ExBool true), (ExNumber 5), (ExBool false))
let bad2 = ExApplication (test5, test3)
let bad3 = ExList ((ExNumber 5), (ExList ((ExBool false), ExNil Int)))
let bad4 = ExOperation (OpEqual, test2, test3)

(* Testes fornecidos pelo professor *)
let tProf1 = ExFunction ("x", Int, ExOperation (OpPlus, ExVar "x", ExVar "y")) (* mal tipada - y não existe em gamma *)
let tProf2 = ExApplication (ExApplication (ExFunction ("x", Int, ExFunction ("y", Int, ExOperation (OpPlus, ExVar "x", ExVar "y"))), ExNumber 3), ExNumber 4) (* int (7) *)
let tProf3 = ExApplication (ExFunction ("x", Int, ExFunction ("y", Int, ExOperation (OpPlus, ExVar "x", ExVar "y"))), ExNumber 3) (* int -> int *)
let tProf4 = ExFunction ("x", Int, ExFunction ("y", Int, ExOperation (OpPlus, ExVar "x", ExVar "y"))) (* int -> int -> int *)
let tProf5 = ExLet ("x", Int, ExNumber 1, 
                    ExLet ("y", Int, 
                           ExOperation (OpPlus, ExNumber 9, ExVar "x"), 
                           ExOperation (OpPlus, 
                                        ExLet ("x", Int, ExNumber 2, 
                                               ExOperation (OpTimes, ExVar "x", ExVar "y")), ExVar "x")))  (*  tipo int (21) *)
let tProf6 = ExLet ("x", Bool, ExBool true, ExLet ("x", Int, ExNumber 10, ExVar "x")) (* tipo int (10) *)   
let tProf8 = ExLetRec ("fat", 
                       Int, 
                       Int, 
                       "x", 
                       Int, 
                       ExIf (ExOperation (OpEqual, ExVar "x", ExNumber 0), 
                             ExNumber 1, 
                             ExOperation (OpTimes, ExVar "x", 
                                          ExApplication (ExVar "fat", ExOperation (OpMinus, ExVar "x", ExNumber 1)))),
                       ExApplication (ExVar "fat", ExNumber 5)
                      )  (* tipo int (120) *)
let tProf9 = ExLetRec ("fat", 
                       Int, 
                       Int, 
                       "x", 
                       Int, 
                       ExIf (ExOperation (OpEqual, ExVar "x", ExNumber 0), 
                             ExNumber 1, 
                             ExOperation (OpTimes, ExVar "x", 
                                          ExApplication (ExVar "fat", ExOperation (OpMinus, ExVar "x", ExNumber 1)))),
                       ExApplication (ExFunction ("f", TyFun (Int, Int), ExVar "f"), ExVar "fat")
                      ) (* tipo int -> int *)
let tProf11 = ExLetRec ("pow", 
                        Int, 
                        TyFun (Int, Int), 
                        "x", 
                        Int, 
                        ExFunction ("y", Int, ExIf (ExOperation (OpEqual, ExVar "y", ExNumber 0), ExNumber 1, ExOperation (OpTimes, ExVar "x", ExApplication (ExApplication (ExVar "pow", ExVar "x"), ExOperation (OpMinus, ExVar "y", ExNumber 1))))),
                        ExApplication (ExApplication (ExVar "pow", ExNumber 3), ExNumber 4)
                       ) (* tipo int (81) *)
let tProf12 = ExLetRec ("pow", 
                        Int, 
                        TyFun (Int, Int), 
                        "x", 
                        Int, 
                        ExFunction ("y", Int, ExIf (ExOperation (OpEqual, ExVar "y", ExNumber 0), ExNumber 1, ExOperation (OpTimes, ExVar "x", ExApplication (ExApplication (ExVar "pow", ExVar "x"), ExOperation (OpMinus, ExVar "y", ExNumber 1))))),
                        ExVar "pow"
                       ) (* tipo int -> (int -> int) *)
let tProf2_1 = ExLet ("x", 
                      Int, 
                      ExNumber 2, 
                      ExLet ("foo", 
                             TyFun (Int, Int), 
                             ExFunction ("y", Int, ExOperation (OpPlus, ExVar("x"), ExVar("y"))), 
                             ExLet ("x", 
                                    Int, 
                                    ExNumber 5, 
                                    ExApplication (ExVar "foo", ExNumber 10)
                                   )
                            )
                     ) (* tipo int (12) *)
let tProf2_2 = ExLet ("x", 
                      Int, 
                      ExNumber 2, 
                      ExLet ("foo", 
                             TyFun (Int, Int), 
                             ExFunction ("y", Int, ExOperation (OpPlus, ExVar("x"), ExVar("y"))), 
                             ExLet ("x", 
                                    Int, 
                                    ExNumber 5,
                                    ExVar "foo"
                                   )
                            )
                     ) (* tipo int -> int *)
let tProf2_3 = ExLetRec ("lookup",
                         TyList (TyPair (Int, Int)),
                         TyFun (Int, TyMaybe Int),
                         "l",
                         TyList (TyPair (Int, Int)),
                         ExFunction ("key", Int, ExMatchL (ExVar "l", ExNothing Int, "x", "xs", ExIf (ExOperation (OpEqual, ExFst (ExVar "x"), ExVar "key"), ExJust (ExSnd (ExVar "x")), ExApplication (ExApplication (ExVar "lookup", ExVar "xs"), ExVar "key")))),
                         ExApplication (ExApplication (ExVar "lookup", ExList (ExPair (ExNumber 1, ExNumber 10), ExList (ExPair (ExNumber 2, ExNumber 20), ExList (ExPair (ExNumber 3, ExNumber 30), ExNil (TyPair (Int, Int)))))), ExNumber 2)
                        ) (* tipo maybe int (just 20) *)
let tProf2_4 = ExLetRec ("map",
                         TyFun (Int, Int),
                         TyFun (TyList Int, TyList Int),
                         "f",
                         TyFun (Int, Int),
                         ExFunction ("l", TyList Int, ExMatchL (ExVar "l",
                                                                ExNil Int,
                                                                "x",
                                                                "xs",
                                                                ExList (ExApplication (ExVar "f", ExVar "x"), ExApplication (ExApplication (ExVar "map", ExVar "f"), ExVar "xs"))
                                                               )),
                         ExApplication (ExApplication (ExVar "map", ExFunction ("x", Int, ExOperation (OpPlus, ExVar "x", ExVar "x"))), ExList (ExNumber 10, ExList (ExNumber 20, ExList (ExNumber 30, ExNil Int))))
                        )
;;

(* Iterador que roda todos os testes. *)
List.iter runTest [
  test1;
  test2;
  test3;
  test4;
  test5;
  test6;
  test7;
  test8;
  test9;
  test10;
  test11;
  test12;
  test13;
  test14;
  test15;
  test16;
  test17;
  test18;
  test19;
  test20;
  testIf;
  testOperation;
  testPair;
  testFst;
  testSnd;
  testList;
  testHd;
  testTl;
  testBoolOperation1;
  testBoolOperation2;
  testBoolOperation3;
  bad1;
  bad2;
  bad3;
  bad4;
  tProf1;
  tProf2;
  tProf3;
  tProf4;
  tProf5;
  tProf6;
  tProf8;
  tProf9;
  tProf11;
  tProf12;
  tProf2_1;
  tProf2_2;
  tProf2_3;
  tProf2_4
]


