structure ContractUtil = struct

exception Error of string

open ContractTypes
open Expr
infix !+! !<! !|!

(* buyer and seller with the currencies they receive,
   notional amount, strike (sell/buy), date of transaction 
   (string,currency) -> (string,currency) 
   -> real -> real -> days -> Contract.t
*) 
fun fxForward (buyer,buyCurr) (seller, otherCurr) amount strike 0 =
            Scale (R amount, 
                   All [ TransfOne (buyCurr, seller, buyer)
                        , Scale ((R strike),
                                 TransfOne (otherCurr, buyer, seller))]
                  )
  | fxForward (buyer,buyCurr) (seller, otherCurr) amount strike days =
    if days > 0 then 
        Transl (I days, 
                fxForward (buyer, buyCurr) (seller, otherCurr) amount strike 0)
    else raise Error "fxForward into the past"

(* buyer and seller with the currencies they receive,
   notional amount, strike (sell/buy), expiry (days), start date (today?) 
   (string,currency) -> (string,currency) 
   -> real -> real -> int -> days -> Contract.t
*) 
fun vanillaFxCall 
        (buyer,buyCurr) (seller, otherCurr) amount strike expiry =
    let val rate    = "FX " ^ Currency.ppCur buyCurr   (* an ad hoc conven- *)
                      ^ "/" ^ Currency.ppCur otherCurr (* tion for rates    *)
        val cond    =  Expr.!<! (obs (rate, 0), R strike)
                      (* option taken depending on price > strike *)
                      (* offset "0", Transl supposed to move obs date offset!*)
    in Transl (I expiry,If (cond, fxForward (buyer, buyCurr) 
                                            (seller, otherCurr) 
                                            amount strike 0    , All []))
    end

fun vanillaFxPut
        (seller, sellCurr) (buyer,otherCurr) amount strike expiry =
    let val rate    = "FX " ^ Currency.ppCur sellCurr  (* an ad hoc conven- *)
                      ^ "/" ^ Currency.ppCur otherCurr (* tion for rates    *)
        val cond    =  Expr.!<! (R strike, obs (rate, 0))
                      (* option taken depending on price < strike *)
                      (* assumes Transl moves obs date offset (see previous) *)
    in Transl (I expiry,If (cond, fxForward (buyer, sellCurr)
                                            (seller, otherCurr)
                                            amount strike 0    , All []))
    end

(* Single-Barrier *-touch options (up or down) require "continuous", i.e.
   daily fixings. 
   Notional value unnecessary, only the fixed coupon of it is used.
   buyer, seller, settling currency, amount, FX cross, barrier, up/down, expiry
*)
datatype BarrierKind = Up | Down

(* First version (BAD) uses recursion in SML, unrolling the entire contract period! *)
fun fxBarrierTouchBAD
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = "FX " ^ Currency.ppCur cur1
                   ^ "/" ^ Currency.ppCur cur2
        val cond = case kind of 
                           Up   => Expr.!<! (R barrier, obs (rate, 0))
                         | Down => Expr.!<! (obs (rate, 0), R barrier)
                      (* next steps depend on whether barrier hit today *)
                      (* note that Transl below leads to checking every day *)
        fun fxTLoop day = 
            Transl (I day, 
                    If (cond,
                        Scale (R amount, TransfOne (curSettle, buyer, seller)),
                        if day < expiry then fxTLoop (day + 1)
                        else All [] (* base case, immediate expiry *)))
    in fxTLoop 0
    end

(* using a tailored loop construct "CheckWithin", much better: no big
   unrolled data structure. Evaluation needs to realise its semantics.
   buyer, seller, settling currency, amount, FX cross, barrier, up/down, expiry
*)
fun fxBarrierTouch
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = "FX " ^ Currency.ppCur cur1
                   ^ "/" ^ Currency.ppCur cur2
        val cond = case kind of
                       Up   => Expr.!<! (R barrier, obs (rate,0))
                     | Down => Expr.!<! (obs (rate,0), R barrier)
                      (* next steps depend on whether barrier hit today *)
                      (* XXX CheckWithin assumed to translate cond accordingly! *)
    in CheckWithin (cond, I expiry, (* XXX var -> cond?? *)
                    Scale (R amount, TransfOne (curSettle, buyer, seller)),
                    All []) (* if barrier hit: payment. Otherwise: empty *)
    end

(* NO-touch options: pay out if barrier NOT breached, just swapping
   the branches from before (exit to empty when touched, pay otherwise).

   Could also again unroll the period in a SML-level recursion.

   buyer, seller, settling currency, amount, FX cross, barrier, up/down, expiry
*)
fun fxBarrierNoTouchBAD
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = "FX " ^ Currency.ppCur cur1
                   ^ "/" ^ Currency.ppCur cur2
        val cond = case kind of (* same code as above, but condition swapped *)
                           Up   => Expr.!<! (obs (rate, 0), R barrier)
                         | Down => Expr.!<! (R barrier, obs (rate, 0))
        fun fxTLoop day = 
            Transl (I day,
                    If (cond, 
                        Scale (R amount, TransfOne (curSettle, buyer, seller)),
                        if day < expiry then fxTLoop (day + 1)
                        else All [] (* base case, immediate expiry *)))
    in fxTLoop 0
    end

fun fxBarrierNoTouch
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = "FX " ^ Currency.ppCur cur1
                   ^ "/" ^ Currency.ppCur cur2
        val cond = case kind of
                       Up   => Expr.!<! (R barrier, obs (rate, 0) )
                     | Down => Expr.!<! (obs (rate, 0), R barrier )
                      (* intention: exit when barrier hit today *)
                      (* XXX CheckWithin assumed to translate cond accordingly! *)
    in CheckWithin (cond, I expiry, (* XXX var -> cond?? *)
                    All [], (* if barrier hit: empty, otherwise: payment *)
                    Scale (R amount, TransfOne (curSettle, buyer, seller)))
    end

(* Single barrier option: easy using CheckWithin and vanillaFX[Put|Call] 
   XXX TODO
*)

(* Double barrier option: we need a boolean "or" (added), then just as
   easy as the single barrier.
   option buyer, option seller, (curr1,curr2) 
       OptionKind(Call/Put) amount strike (lo-barrier, hi-barrier) expiry
*)
datatype OptionKind = Call | Put

fun fxDoubleBarrierIn 
    buyer seller (cur1,cur2) optKind amount strike (loBarr,hiBarr) expiry
  = let val rate = "FX " ^ Currency.ppCur cur1
                   ^ "/" ^ Currency.ppCur cur2
        val cond = (obs (rate,0) !<! (R loBarr))
                   !|! ((R hiBarr) !<! obs (rate,0))
                    (* "in" if price below lower || above upper *)
        val result = case optKind of
                         Call => vanillaFxCall
                       | Put  => vanillaFxPut
    in CheckWithin (cond, I expiry,
                    result (buyer,cur1) (seller,cur2) amount strike expiry,
                    All []) (* if barrier hit: option; otherwise empty *)
    end

end
