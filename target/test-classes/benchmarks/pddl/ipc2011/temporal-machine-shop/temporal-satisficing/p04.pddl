(define (problem pfile3)
 (:domain domain-tms-2-3-light)
 (:objects 
 kiln0 - kiln8
 kiln0 - kiln20
 pone0 pone1 pone2 pone3 pone4 pone5 pone6 pone7 pone8 pone9 pone10 pone11 pone12 pone13 pone14 pone15 - piecetype1
 ptwo0 ptwo1 ptwo2 ptwo3 ptwo4 ptwo5 ptwo6 ptwo7 ptwo8 ptwo9 ptwo10 ptwo11 ptwo12 ptwo13 ptwo14 ptwo15 ptwo16 ptwo17 ptwo18 ptwo19 ptwo20 ptwo21 ptwo22 ptwo23 - piecetype2
 pthree0 pthree1 pthree2 pthree3 pthree4 pthree5 pthree6 pthree7 pthree8 pthree9 pthree10 pthree11 pthree12 pthree13 pthree14 pthree15 pthree16 pthree17 pthree18 pthree19 pthree20 pthree21 pthree22 pthree23 pthree24 pthree25 pthree26 pthree27 pthree28 pthree29 pthree30 pthree31 pthree32 pthree33 pthree34 pthree35 pthree36 pthree37 pthree38 pthree39 - piecetype3
)
 (:init 
  (energy)
)
 (:goal
  (and
     (baked-structure ptwo21 ptwo9)
     (baked-structure ptwo19 pthree32)
     (baked-structure pone7 pthree15)
     (baked-structure pthree33 pthree3)
     (baked-structure pthree0 ptwo0)
     (baked-structure ptwo15 pone4)
     (baked-structure pthree11 pthree38)
     (baked-structure pthree13 pone1)
     (baked-structure pthree34 pthree5)
     (baked-structure ptwo3 ptwo7)
     (baked-structure ptwo18 ptwo6)
     (baked-structure pthree10 ptwo13)
     (baked-structure pthree19 pone5)
     (baked-structure ptwo10 ptwo12)
     (baked-structure pthree18 pone2)
     (baked-structure ptwo4 pthree2)
     (baked-structure pone12 pthree4)
     (baked-structure pthree8 pone10)
     (baked-structure pthree17 pone9)
     (baked-structure pthree28 pone3)
     (baked-structure pthree39 ptwo8)
     (baked-structure ptwo23 pthree23)
     (baked-structure ptwo5 pthree1)
     (baked-structure pthree9 ptwo1)
     (baked-structure pone13 pthree22)
     (baked-structure pone15 pthree14)
     (baked-structure pthree37 pone11)
     (baked-structure ptwo20 pthree21)
     (baked-structure ptwo11 pthree30)
     (baked-structure ptwo14 pthree26)
     (baked-structure ptwo2 pthree29)
     (baked-structure pthree20 pthree31)
     (baked-structure pone6 ptwo16)
     (baked-structure pone0 pthree12)
     (baked-structure ptwo17 pthree24)
     (baked-structure pone14 pthree7)
     (baked-structure pthree6 ptwo22)
     (baked-structure pone8 pthree25)
     (baked-structure pthree35 pthree16)
     (baked-structure pthree27 pthree36)
))
 (:metric minimize (total-time))
)