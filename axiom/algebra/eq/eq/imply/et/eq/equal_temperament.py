from util import *


@apply
def apply(eq_1_high, et_eq):
    λ_1_high, λ_1 = eq_1_high.of(Equal[Expr / Expr, S.One / 2])
    
    eq_12_22, eq_23_34, eq_34_44, eq_45_55, eq_56_66, eq_67_71, eq_11_12, eq_22_23, eq_44_45, eq_55_56, eq_66_67  = et_eq.of(And)
    r_11, r_12 = eq_11_12.of(Equal)    
    
    _r_12, r_22 = eq_12_22.of(Equal)
    assert _r_12 == r_12
    
    _r_22, r_23 = eq_22_23.of(Equal)
    assert _r_22 == r_22
    
    _r_23, r_34 = eq_23_34.of(Equal)
    assert _r_23 == r_23
    
    _r_34, r_44 = eq_34_44.of(Equal)
    assert _r_34 == r_34
        
    _r_44, r_45 = eq_44_45.of(Equal)
    assert _r_44 == r_44
    
    _r_45, r_55 = eq_45_55.of(Equal)
    assert _r_45 == r_45
    
    _r_55, r_56 = eq_55_56.of(Equal)
    assert _r_55 == r_55
    
    _r_56, r_66 = eq_56_66.of(Equal)
    assert _r_56 == r_56
    
    _r_66, r_67 = eq_66_67.of(Equal)
    assert _r_66 == r_66
    
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
    
    λ_5, _λ_4_sharp = r_45.of(Expr / Expr)
    assert _λ_4_sharp == λ_4_sharp
    
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
    
    w = (S.One / 2) ** (S.One / 12)
    return Equal(λ_1_sharp / λ_1, w), Equal(λ_4 / λ_3, w), Equal(λ_2 / λ_1, w ** 2), Equal(λ_4 / λ_1, w ** 5)


@prove
def prove(Eq):
    from axiom import algebra

    λ_1, λ_2, λ_3, λ_4, λ_5, λ_6, λ_7 = Symbol(real=True, positive=True)
    λ_1_sharp = Symbol("λ_{1^\#}", real=True, positive=True)
    λ_2_sharp = Symbol("λ_{2^\#}", real=True, positive=True)
    λ_4_sharp = Symbol("λ_{4^\#}", real=True, positive=True)
    λ_5_sharp = Symbol("λ_{5^\#}", real=True, positive=True)
    λ_6_sharp = Symbol("λ_{6^\#}", real=True, positive=True)
    λ_1_high = Symbol("λ_\dot{1}", real=True, positive=True)
    Eq << apply(Equal(λ_1_high / λ_1, S.One / 2),
                And(Equal(λ_1_sharp / λ_1, λ_2 / λ_1_sharp), Equal(λ_2 / λ_1_sharp, λ_2_sharp / λ_2), Equal(λ_2_sharp / λ_2, λ_3 / λ_2_sharp), Equal(λ_3 / λ_2_sharp, λ_4 / λ_3), Equal(λ_4 / λ_3, λ_4_sharp / λ_4), Equal(λ_4_sharp / λ_4, λ_5 / λ_4_sharp), Equal(λ_5 / λ_4_sharp, λ_5_sharp / λ_5), Equal(λ_5_sharp / λ_5, λ_6 / λ_5_sharp), Equal(λ_6 / λ_5_sharp, λ_6_sharp / λ_6), Equal(λ_6_sharp / λ_6, λ_7 / λ_6_sharp), Equal(λ_7 / λ_6_sharp, λ_1_high / λ_7)))

    w = Symbol(λ_1_sharp / λ_1)
    Eq.r_1_sharp = w.this.definition.reversed

    Eq << algebra.et.imply.et.apply(Eq[1], None)

    Eq.r_2 = Eq[12].subs(Eq.r_1_sharp).reversed

    Eq.r_2_sharp = Eq[6].subs(Eq.r_2).reversed

    Eq.r_3 = Eq[13].subs(Eq.r_2_sharp).reversed

    Eq.r_4 = Eq[7].subs(Eq.r_3).reversed

    Eq.r_4_sharp = Eq[8].subs(Eq.r_4).reversed

    Eq.r_5 = Eq[14].subs(Eq.r_4_sharp).reversed

    Eq.r_5_sharp = Eq[9].subs(Eq.r_5).reversed

    Eq.r_6 = Eq[15].subs(Eq.r_5_sharp).reversed

    Eq.r_6_sharp = Eq[10].subs(Eq.r_6).reversed

    Eq.r_7 = Eq[16].subs(Eq.r_6_sharp).reversed

    Eq.r_1_high = Eq[11].subs(Eq.r_7).reversed

    Eq << Eq.r_1_sharp * Eq.r_2_sharp * Eq.r_4_sharp * Eq.r_5_sharp * Eq.r_6_sharp * Eq.r_2 * Eq.r_3 * Eq.r_4 * Eq.r_5 * Eq.r_6 * Eq.r_7 * Eq.r_1_high

    Eq << Eq[-1].subs(Eq[0]).reversed

    Eq << Eq[-1] ** (S.One / 12)

    Eq << Eq.r_1_sharp.subs(Eq[-1])

    Eq << Eq.r_4.subs(Eq[-1])

    Eq << (Eq.r_1_sharp * Eq.r_2).subs(Eq[-1])

    Eq << (Eq.r_1_sharp * Eq.r_2 * Eq.r_2_sharp * Eq.r_3 * Eq.r_4).subs(Eq[-1])

    #十二平均律的基本假设是：
    #一，纯八度之间的波长之比为1/2, 即等式Eq[0]成立;
    #二，5个升降音与还原音之间的波长比相等，7个还原音与之前一个半音之间的波长比相等，且这两个比例相同，即等式组Eq[1]成立;
    #根据以上两点可以推导：
    #一，一个升降音与还原间波长比为2**(11/12)/2=0.9438743126816935,
    #比较与纯律得出的值   2048/2187=0.9364426154549611，基本相同;
    #二，一个小二度使波长变为原来的2**(11/12)/2=0.9438743126816935，
    #比较与纯律得出的值     243/256=0.94921875，也基本相同；
    #三，一个大二度使波长变为原来的2**(5/6)/2=0.8908987181403393,
    #比较与纯律得出的值       8/9=0.8888888888888888, 基本相同；
    #四，一个纯四度使波长变为原来的2**(7/12)/2=0.7491535384383408，
    #比较与纯律得出的值        3/4=0.75，基本相同；
    #如果想得出各音阶频率之比，可以从波长之比的倒数得出，且对于弦乐器，弦长之比等于波长之比。
    #参考资料：律学新说，https://baike.baidu.com/item/%E5%BE%8B%E5%AD%A6%E6%96%B0%E8%AF%B4/5626236?fr=aladdin
    
    


if __name__ == '__main__':
    run()
# created on 2018-10-10
# updated on 2021-11-19