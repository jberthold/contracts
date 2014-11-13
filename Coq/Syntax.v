Require Export Reals.
Require Export String.
Require Export Utils.
Require Export DecidableType.

Declare Module Currency:DecidableType.
Declare Module Party:DecidableType.

Definition currency := Currency.t.
Definition party := Party.t.


Inductive Var : Set := V1 | VS (v:Var).

Inductive ObsLabel : Set := LabR (l:string) | LabB (l:string).

Inductive Op : Set := Add | Sub | Mult | Div | And | Or | Less | Leq | Equal |
                      Not | Neg |
                      BLit (b : bool) | RLit (r:R) |
                      Cond.



Inductive Exp : Set := OpE (op : Op) (args : list Exp)
                     | Obs (l:ObsLabel) (i: Z)
                     | VarE (v:Var)
                     | Acc (f : Exp) (d : nat) (e : Exp).


Definition Exp_ind'   : forall P : Exp -> Prop,
       (forall (op : Op) (args : list Exp), forall_list P args -> P (OpE op args)) ->
       (forall (l : ObsLabel) (i : Z), P (Obs l i)) ->
       (forall v : Var, P (VarE v)) ->
       (forall f2 : Exp,
        P f2 -> forall (d : nat) (e : Exp), P e -> P (Acc f2 d e)) ->
       forall e : Exp, P e := 
fun (P : Exp -> Prop)
  (f : forall (op : Op) (args : list Exp), forall_list P args -> P (OpE op args))
  (f0 : forall (l : ObsLabel) (i : Z), P (Obs l i))
  (f1 : forall v : Var, P (VarE v))
  (f2 : forall f2 : Exp,
        P f2 -> forall (d : nat) (e : Exp), P e -> P (Acc f2 d e)) =>
fix F (e : Exp) : P e :=
  match e as e0 return (P e0) with
  | OpE op args => let fix step es : forall_list P es := 
                       match es with
                           | nil => forall_nil P
                           | e' :: es' => forall_cons P (F e') (step es')
                       end
                   in  f op args (step args)
  | Obs l i => f0 l i
  | VarE v => f1 v
  | Acc f3 d e0 => f2 f3 (F f3) d e0 (F e0)
  end.


Inductive Contr : Type :=
 | Zero : Contr
 | Transfer : party -> party -> currency -> Contr
 | Scale : Exp -> Contr -> Contr
 | Translate : nat -> Contr -> Contr
 | Both : Contr -> Contr -> Contr
 | If : Exp -> nat -> Contr -> Contr -> Contr.


Definition translate (l : nat) : Contr -> Contr := 
  match l with
    | O => (fun x => x)
    | _ => Translate l
  end.
