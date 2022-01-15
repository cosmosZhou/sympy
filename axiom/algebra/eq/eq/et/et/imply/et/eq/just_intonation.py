from util import *


@apply
def apply(eq_1_high, eq_5, et_b, et_w):
    λ_1_high, λ_1 = eq_1_high.of(Equal[Expr / Expr, S.One / 2])
    λ_5, _λ_1 = eq_5.of(Equal[Expr / Expr, Number(2) / 3])
    assert _λ_1 == λ_1
    
    eq_11_22, eq_22_44, eq_44_55, eq_55_66 = et_b.of(And)
    r_11, r_22 = eq_11_22.of(Equal)
    _r_22, r_44 = eq_22_44.of(Equal)
    assert _r_22 == r_22
    _r_44, r_55 = eq_44_55.of(Equal)
    assert _r_44 == r_44
    _r_55, r_66 = eq_55_66.of(Equal)
    assert _r_55 == r_55
    
    eq_12_23, eq_23_34, eq_34_45, eq_45_56, eq_56_67, eq_67_71 = et_w.of(And)
    r_12, r_23 = eq_12_23.of(Equal)
    _r_23, r_34 = eq_23_34.of(Equal)
    assert _r_23 == r_23
    _r_34, r_45 = eq_34_45.of(Equal)
    assert _r_34 == r_34
    _r_45, r_56 = eq_45_56.of(Equal)
    assert _r_45 == r_45
    _r_56, r_67 = eq_56_67.of(Equal)
    assert _r_56 == r_56
    _r_67, r_71 = eq_67_71.of(Equal)
    assert _r_67 == r_67
    
    λ_1_sharp, _λ_1 = r_11.of(Expr / Expr)
    assert _λ_1 == λ_1
    λ_2, _λ_1_sharp = r_12.of(Expr / Expr)
    assert _λ_1_sharp == λ_1_sharp
    
    λ_2_sharp, _λ_2 = r_22.of(Expr / Expr)
    assert _λ_2 == λ_2
    
    λ_3, _λ_2_sharp = r_23.of(Expr / Expr)
    assert _λ_2_sharp == λ_2_sharp
    
    λ_4, _λ_3 = r_34.of(Expr / Expr)
    assert _λ_3 == λ_3
    
    λ_4_sharp, _λ_4 = r_44.of(Expr / Expr)
    assert _λ_4 == λ_4
    
    _λ_5, _λ_4_sharp = r_45.of(Expr / Expr)
    assert _λ_4_sharp == λ_4_sharp
    assert _λ_5 == λ_5
    
    λ_5_sharp, _λ_5 = r_55.of(Expr / Expr)
    assert _λ_5 == λ_5
    
    λ_6, _λ_5_sharp = r_56.of(Expr / Expr)
    assert _λ_5_sharp == λ_5_sharp
    
    λ_6_sharp, _λ_6 = r_66.of(Expr / Expr)
    assert _λ_6 == λ_6
    
    λ_7, _λ_6_sharp = r_67.of(Expr / Expr)
    assert _λ_6_sharp == λ_6_sharp
        
    _λ_1_high, _λ_7 = r_71.of(Expr / Expr)
    assert _λ_7 == λ_7
    assert _λ_1_high == λ_1_high
    
    return Equal(λ_1_sharp / λ_1, Number(2) ** 11 / 3 ** 7), Equal(λ_4 / λ_3, Number(3) ** 5 / 2 ** 8), Equal(λ_2 / λ_1, Number(8) / 9), Equal(λ_4 / λ_1, Number(3) / 4)


@prove
def prove(Eq):
    from axiom import algebra

    λ_1, λ_2, λ_3, λ_4, λ_5, λ_6, λ_7 = Symbol(real=True)
    λ_1_sharp = Symbol("λ_{1^\#}", real=True)
    λ_2_sharp = Symbol("λ_{2^\#}", real=True)
    λ_4_sharp = Symbol("λ_{4^\#}", real=True)
    λ_5_sharp = Symbol("λ_{5^\#}", real=True)
    λ_6_sharp = Symbol("λ_{6^\#}", real=True)
    λ_1_high = Symbol("λ_\dot{1}", real=True)
    Eq << apply(Equal(λ_1_high / λ_1, S.One / 2), Equal(λ_5 / λ_1, Number(2) / 3),
                And(Equal(λ_1_sharp / λ_1, λ_2_sharp / λ_2), Equal(λ_2_sharp / λ_2, λ_4_sharp / λ_4), Equal(λ_4_sharp / λ_4, λ_5_sharp / λ_5), Equal(λ_5_sharp / λ_5, λ_6_sharp / λ_6)),
                And(Equal(λ_2 / λ_1_sharp, λ_3 / λ_2_sharp), Equal(λ_3 / λ_2_sharp, λ_4 / λ_3), Equal(λ_4 / λ_3, λ_5 / λ_4_sharp), Equal(λ_5 / λ_4_sharp, λ_6 / λ_5_sharp), Equal(λ_6 / λ_5_sharp, λ_7 / λ_6_sharp), Equal(λ_7 / λ_6_sharp, λ_1_high / λ_7)))

    b = Symbol(λ_1_sharp / λ_1)
    w = Symbol(λ_2 / λ_1_sharp)
    Eq.r_1_sharp = b.this.definition.reversed

    Eq << algebra.et.imply.et.apply(Eq[2], None)

    Eq.r_2_sharp = Eq[-4].subs(Eq.r_1_sharp).reversed

    Eq.r_4_sharp = Eq[-3].subs(Eq.r_2_sharp).reversed

    Eq.r_5_sharp = Eq[-2].subs(Eq.r_4_sharp).reversed

    Eq.r_6_sharp = Eq[-1].subs(Eq.r_5_sharp).reversed

    Eq.r_2 = w.this.definition.reversed

    Eq << algebra.et.imply.et.apply(Eq[3], None)

    Eq.r_3 = Eq[-6].subs(Eq.r_2).reversed

    Eq.r_4 = Eq[-5].subs(Eq.r_3).reversed

    Eq.r_5 = Eq[-4].subs(Eq.r_4).reversed

    Eq.r_6 = Eq[-3].subs(Eq.r_5).reversed

    Eq.r_7 = Eq[-2].subs(Eq.r_6).reversed

    Eq.r_1_high = Eq[-1].subs(Eq.r_7).reversed

    Eq << Eq.r_1_sharp * Eq.r_2_sharp * Eq.r_4_sharp * Eq.r_5_sharp * Eq.r_6_sharp * Eq.r_2 * Eq.r_3 * Eq.r_4 * Eq.r_5 * Eq.r_6 * Eq.r_7 * Eq.r_1_high

    Eq << Eq[-1].subs(Eq[0]).reversed

    Eq << Eq.r_2 * Eq.r_3 * Eq.r_4 * Eq.r_5 * Eq.r_1_sharp * Eq.r_2_sharp * Eq.r_4_sharp

    Eq << Eq[-1].subs(Eq[1]).reversed

    Eq << Eq[-3] / Eq[-1]

    Eq << Eq[-2] / Eq[-1]

    Eq << Eq[-2] / Eq[-1] ** 2

    Eq << Eq[-2] / Eq[-1]

    Eq << Eq[5].subs(Eq[-2].reversed)

    Eq << Eq[4].subs(Eq.r_1_sharp)

    Eq << (Eq.r_2 * Eq.r_3 * Eq.r_4 * Eq.r_1_sharp * Eq.r_2_sharp).subs(Eq[-1], Eq[-2])

    Eq << (Eq.r_2 * Eq.r_1_sharp).subs(Eq[-1], Eq[-2])

    #针对纯律，我的基本假设是：
    #一，纯八度之间的波长之比为1/2, 即等式Eq[0]成立;
    #二，根据三分损宜法，五度相生律，纯5度之间的波长之比为2/3，即等式Eq[1]成立;
    #三，5个升降音与还原音之间的波长比相等，即等式组Eq[2]成立;
    #四，7个还原音与之前一个半音之间的波长比相等，即等式组Eq[3]成立;
    #根据以上四点可以推导：
    #一，一个升降音与还原间波长比为2048/2187;
    #二，一个小二度使波长/弦长变为原来的243/256；
    #三，一个大二度使波长/弦长变为原来的8/9；
    #四，一个纯四度使波长/弦长变为原来的3/4；
    #百科参考资料：https://baike.baidu.com/pic/%E7%BA%AF%E5%BE%8B/659996/0/834344afb490879efaed5021?fr=lemma&ct=single#aid=0&pic=834344afb490879efaed5021
    
    


if __name__ == '__main__':
    run()
# created on 2018-01-17
# updated on 2021-11-19