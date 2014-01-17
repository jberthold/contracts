infix  7  !*!
infix  6  !+! !-!
infix  5  !|!
infix  4  !=! !<!

open ContractSafe

val today = DateUtil.? "2014-01-01"
fun ctestE s c f E =
    Utest.testPP ppContr s c (fn () =>
                               let val c = f()
                               in #2(simplify E (today,c))
                               end)

val E0 = emptyFrom today
fun ctest s c f = ctestE s c f E0

val () = ctest "zero scale" zero (fn () => scale(R 3.0,zero))
val () = ctest "zero both" zero (fn () => both(zero,scale(R 3.0,zero)))

fun iter n f a = if n < 0 then a else iter (n-1) f (f(n,a))
val pay1EUR = transfOne(EUR,"me","you")
val equity = "Carlsberg"
infix ++
fun d ++ i = DateUtil.addDays i d

val () =
    let val y1 = 360
        val x = new "x"
        val hit = transl(y1,pay1EUR)
        val f = (x, V x !|! (R 50.0 !<! obs(equity,0)))
        fun barrier() =
            iff(acc(f, y1, B false),
                hit,
                zero)
        val E_no = iter 1000 (fn (i,e) => addFixing((equity,today++i,20.0),e)) E0
        val E_hit = iter 1000 (fn (i,e) => addFixing((equity,today++i,real (i div 7)),e)) E0
    in ctestE "barrier - no hit" zero barrier E_no
     ; ctestE "barrier - hit" hit barrier E_hit
    end

(* Requires let-binding...
val () =
    let val maxInt = 100000
        fun translE(e: intE,c) =
            checkWithin(obs("Time",0) !=! e, maxInt, c, zero)
        val E = iter 1000 (fn (i,e) => addFixing((equity,today++i,real i),e)) E0
    in ctestE "translE" pay1EUR (fn () => translE(obs(equity,5), pay1EUR)) E
    end
*)