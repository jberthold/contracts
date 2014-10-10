Require Import Denotational.

(* Specialisation (a.k.a. partial evaluation) of contracts. *)

Definition constFoldBin {n} (op : BinOp) (e1 e2 : rexp' n) : rexp' n :=
  match e1 with
    | RLit _ r1 => match e2 with
                     | RLit _ r2 => RLit (RBinOp op r1 r2)
                     | _ => RBin op e1 e2
                   end
    | e1 => RBin op e1 e2
  end.


Fixpoint constFoldAcc {V} (rho : obs) (f : obs -> R -> rexp' V)  (l : nat) (z : obs -> rexp' V) :
  rexp' V + (nat * rexp' V) :=
  match l with
    | O => inl (z rho)
    | S l' => match constFoldAcc (adv_inp (-1) rho) f l'  z with
                | inl (RLit _ r) => inl (f rho r)
                | inl e => inr (O, e)
                | inr (n, e) => inr (S n, e)
              end
end.

Definition obs_empty : obs := fun _ _ => None.

Fixpoint Rspecialise' {V V'} (e : rexp' V) (rho : obs) : PEnv R V V' -> rexp' V' :=
    match e with
      | RLit _ r => fun _ => RLit r
      | RBin _ op e1 e2 => fun vars => constFoldBin op (Rspecialise' e1 rho vars) (Rspecialise' e2 rho vars)
      | RNeg _ e => fun vars =>
                      match Rspecialise' e rho vars with
                        | RLit _ r => RLit (- r)
                        | e => RNeg e
                      end
      | Obs _ obs t => fun vars =>
                         match rho t obs with
                           | Some r => RLit r
                           | None => Obs obs t
                         end
      | RVar _ v => fun vars =>
                      match lookupPEnv vars v with
                        | inl r =>  RLit r
                        | inr v' => RVar v'
                      end
      | RAcc _ f l z => fun vars =>
                        let z' rho := Rspecialise' z rho vars in
                        let f' rho r := Rspecialise' f rho (PExtend r vars)
                        in match constFoldAcc rho f' l z' with
                             | inl e => e
                             | inr (l', e') => RAcc (Rspecialise' f obs_empty (PSkip vars)) l' e'
                           end
    end.


Definition Rspecialise (e : rexp) (o : obs) : rexp := Rspecialise' e o (PEmpty (zero R)).


Fixpoint constFoldBAcc {V} (rho : ext) (f : ext -> bool -> bexp' V)  (l : nat) (z : ext -> bexp' V) :
  bexp' V + (nat * bexp' V) :=
  match l with
    | O => inl (z rho)
    | S l' => match constFoldBAcc (adv_ext (-1) rho) f l'  z with
                | inl (BLit _ b) => inl (f rho b)
                | inl e => inr (O, e)
                | inr (n, e) => inr (S n, e)
              end
end.

Definition choices_empty : choices := fun _ _ => None.

Definition ext_empty : ext := (obs_empty,choices_empty).


Definition constFoldBOp {V} (op : BoolOp) (e1 e2 : bexp' V) : bexp' V :=
  match e1 with
    | BLit _ b1 => match e2 with
                     | BLit _ b2 => BLit (BBinOp op b1 b2)
                     | _ => BOp op e1 e2
                   end
    | _ => BOp op e1 e2
  end.


Fixpoint Bspecialise' {V V'} (e : bexp' V) (rho : ext) : PEnv bool V V' -> bexp' V' :=
  match e with
    | BLit _ b => fun _ => BLit b
    | BChoice _ ch t => fun vars => match snd rho t ch with
                           | Some b => BLit b
                           | None => BChoice ch t
                         end
    | RCmp _ cmp e1 e2 => fun vars => match Rspecialise e1 (fst rho), Rspecialise e2 (fst rho) with
                          | RLit _ b1, RLit _ b2 => BLit (RCompare cmp b1 b2)
                          | e1',e2' => RCmp cmp e1' e2'
                        end
    | BNot _ e' => fun vars => match Bspecialise' e' rho vars with
                   | BLit _ b => BLit (negb b)
                   | e'' => BNot e''
                 end
    | BOp _ op e1 e2 => fun vars => constFoldBOp op (Bspecialise' e1 rho vars) (Bspecialise' e2 rho vars)
    | BVar _ v => fun vars =>
                    match lookupPEnv vars v with
                      | inl r =>  BLit r
                      | inr v' => BVar v'
                    end
    | BAcc _ f l z => fun vars =>
                        let z' rho := Bspecialise' z rho vars in
                        let f' rho r := Bspecialise' f rho (PExtend r vars)
                        in match constFoldBAcc rho f' l z' with
                             | inl e => e
                             | inr (l', e') => BAcc (Bspecialise' f ext_empty (PSkip vars)) l' e'
                           end
                                      
  end.

Definition Bspecialise (e : bexp) (rho : ext) : bexp := Bspecialise' e rho (PEmpty (zero bool)).

Fixpoint traverseIfWithin (rho : ext) (e: bexp) (c1 c2 : ext -> contract) (l : nat) : contract + (bexp * nat) :=
  match Bspecialise e rho with
      | BLit _ true => inl (c1 rho)
      | BLit _ false => match l with
                        | O => inl (c2 rho)
                        | S l' => traverseIfWithin (adv_ext 1 rho) e c1 c2 l'
                        end
      | e' => inr (e', l)
  end.

Fixpoint specialise (c : contract) (rho : ext) : contract :=
  match c with
    | Zero => c
    | TransfOne _ _ _ => c
    | Scale e c' => Scale (Rspecialise e (fst rho)) c'
    | Transl l c' => Transl l (specialise c' (adv_ext (Z.of_nat l) rho))
    | Both c1 c2 => Both (specialise c1 rho) (specialise c2 rho)
    | IfWithin e l c1 c2 => match traverseIfWithin rho e (specialise c1) (specialise c2) l with
                              | inl c' => c'
                              | inr (e', l') => transl (l - l') (IfWithin e' l' c1 c2)
                            end
  end.