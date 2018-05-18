package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.ODEInvariance._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

class ODEInvarianceTests extends TacticTestBase {

  "ODEInvariance" should "prove the helper axioms" in withMathematica { qeTool =>
    uniqMin shouldBe 'proved
    refMaxL shouldBe 'proved
    refMaxR shouldBe 'proved
    uniqAx shouldBe 'proved
    contAx shouldBe 'proved
  }

  it should "compute bounded p*>0" in withMathematica { qeTool =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asDifferentialProgram
    val poly = "x+y*z".asTerm
    val p0 = pStar(ode,poly,0)
    val p1 = pStar(ode,poly,1)
    val p2 = pStar(ode,poly,2)
    val p3 = pStar(ode,poly,3)

    //println(p0)
    //println(p1)
    //println(p2)
    //println(p3)
    p0 shouldBe "x+y*z>0".asFormula
    p1 shouldBe "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>0)".asFormula
    p2 shouldBe "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>0))".asFormula
    p3 shouldBe "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>=0&(2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)=0->2+6*x^4+12*y+12*y^2+8*(1+y)*z+2*x^3*(6+y+2*z)+4*x^2*(8+3*y+2*z)+x*(12+37*y+18*z)>0)))".asFormula
  }

  it should "compute bounded P*" in withMathematica { qeTool =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asDifferentialProgram
    val poly = "max(min(z,min(x,y)),min(x,y))".asTerm
    val p0 = pStarHom(ode,poly,0)
    val p1 = pStarHom(ode,poly,1)
    val p2 = pStarHom(ode,poly,2)
    val p3 = pStarHom(ode,poly,3)
    //Huge mess of a formula here
    println(p0,p1,p2,p3)
  }

  it should "take a local progress step" in withMathematica { qeTool =>
    val seq = "x>=0 ==> <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0, <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0".asSequent
    val pr = proveBy(seq, lpstep(2))
    println(pr)
  }

  it should "do full local progress p>=0" in withMathematica { qeTool =>
    val seq = "x>=0 ==> <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0".asSequent
    val pr = proveBy(seq,
      cut(pStar("{z'=2,x'=x+1,y'=1}".asDifferentialProgram,"x".asTerm,10))
      <(
        cohide2(-2,1) & lpgeq(10),
        cohideOnlyR('Rlast) & QE
      ))
    println(pr)
    pr shouldBe 'proved
  }

  it should "do full local progress with max(min) >=0" in withMathematica { qeTool =>
    val seq = "max(min(z,min(x,y)),min(x,y))>=0 ==> <{t_'=1,x'=x^2+1, y'=2*x+y, z'=x+y+z & max(min(z,min(x,y)),min(x,y)) >= 0}>t_!=0".asSequent
    val t = "max(min(z,min(x,y)),min(x,y))".asTerm
    val pr = proveBy(seq,
      cut(pStarHom("{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asDifferentialProgram,t,4))
        <(
        cohide2(-2,1) & lpclosed(4,t),
        cohideOnlyR('Rlast) & QE
      ))
    println(pr)
    pr shouldBe 'proved
  }

  it should "package with real induction" in withMathematica { qeTool =>
    val fml = "-x<=0 & -y<=0 | x+y<=1 | y>=0 -> [{z'=2,x'=x+1,y'=1&x^2+y^2<1}] (-x<=0 & -y<=0 | x+y<=1 | y>=0)".asFormula
    val pr = proveBy(fml, implyR(1) & sAIclosedPlus(0)(1))
    println(pr)
    pr shouldBe 'proved
  }

  it should "try some invariants (1)" in withMathematica { qeTool =>
    val fml = "x^2+y^2>=1 -> [{x'=x-y^3, y'=x^3+y}]!(x^2+y^2<1/2)".asFormula
    val pr = proveBy(fml, implyR(1) &
      dC("(2*(x^2+y^2)-1>=0)".asFormula)(1) <(
        dW(1) & QE,
        sAIclosedPlus()(1) & QE
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "try some invariants (2)" in withMathematica { qeTool =>
    val fml = "x=-1 & y=-1 -> [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asFormula
    //This is an invariant which cannot be proved by the current tactic
    //But it could be proved by re-ordering in a smarter way
    val pr = proveBy(fml, implyR(1) &
      dC("((x<=0&x^2<=2*x*y)&y<=0)".asFormula)(1) <(
        dW(1) & QE,
        (?(sAIclosedPlus(3)(1)))
      )
    )
    println(pr)
    //pr shouldBe 'proved
  }

  it should "try some invariants (3)" in withMathematica { qeTool =>
    //The disjunct x=0 should become "trivial" in the progress proof
    val fml = "x <=0 | x=0 -> [{x'=x-1}] (x <=0 | x=0)".asFormula
    val pr = proveBy(fml, implyR(1) &
        sAIclosedPlus(3)(1)
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "try some invariants (4)" in withMathematica { qeTool =>
    val fml = "(((y<=0&x<=0)&3*x<=2*y)&x<=1+y) -> [{x'=315*x^7+477*x^6*y-113*x^5*y^2+301*x^4*y^3-300*x^3*y^4-192*x^2*y^5+128*x*y^6-16*y^7,\n    y'=y*(2619*x^6-99*x^5*y-3249*x^4*y^2+1085*x^3*y^3+596*x^2*y^4-416*x*y^5+64*y^6)}] (((y<=0&x<=0)&3*x<=2*y)&x<=1+y)".asFormula
    //Again, requires higher DG
    val pr = proveBy(fml, implyR(1) &
      sAIclosedPlus(1)(1)
    )
    println(pr)
  }

  it should "compute aggressive P*" in withMathematica { qeTool =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asDifferentialProgram
    val dom = "c=0".asFormula
    val poly = "max(min(z,min(x,y)),min(x,-abs(z)))".asTerm
    val p1 = pStarHomPlus(ode,dom,poly,1)
    println(p1)
  }

  it should "aggressively try rank 1" in withMathematica { qeTool =>
    val ode = "{x'=x*(x-2*y), y'=-(2*x-y)*y}".asDifferentialProgram
    val fml = "((x<=0&x^2-2*x*y<=0)&y<=0)".asFormula
    val res = rankOneFml(ode,True,fml)
    println(res)
  }

  it should "try rank 1 invariants" in withMathematica { qeTool =>
    val fml = "x=-1 & y=-1 -> [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asFormula
    //This is an invariant which cannot be proved by the current tactic
    //It requires a higher dimensional DG
    val pr = proveBy(fml, implyR(1) &
      dC("(x^2<=2*x*y)&x<=0&y<=0".asFormula)(1) <(
        dW(1) & QE,
        sAIRankOne(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "try a (very) difficult invariant" in withMathematica { qeTool =>
    val fml = "1/100 - x^2 - y^2 >= 0 -> [{x'=-2*x+x^2+y, y'=x-2*y+y^2 & x!=0 | y!=0}]!(x^2+y^2 >= 1/4)".asFormula
    //Original question did not have x!=0 | y!=0 constraint
    //Pegasus invariant: ((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)&-1+4*x^2+4*y^2 < 0
    //However, the equilibrium point at the origin for x*y<=x^2+y^2 is insurmountable for all current tactics
//    val pr = proveBy(fml, implyR(1) &
//      dC("((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)".asFormula)(1) <(
//        dW(1),
//        sAIclosedPlus(1)(1)
//      )
//    )

    //The actual invariant:
    val pr2 = proveBy(fml, implyR(1) &
      dC("x^2+y^2=0 | x^2+y^2!=0 & ((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)&-1+4*x^2+4*y^2 < 0".asFormula)(1) <(
        dW(1) & QE,
        sAIRankOne(1)
      )
    )
    println(pr2)
  }

  it should "prove van der pol" in withMathematica { qeTool =>
    val fml = "1.25<=x&x<=1.55 & 2.35<=y&y<=2.45 -> [{x'=y, y'=y-x-x^2*y, t'=1 & 0<=t&t<=7}]!(y>=2.75)".asFormula
    //The actual invariant:
    val pr = proveBy(fml, implyR(1) &
      dC("0.20595*x^4*y - 0.15329*x^4 - 1.1185*x^3*y + 1.7568*x^2*y^2 - 0.73732*x*y^3 + 0.13061*y^4 - 0.18577*x^3 - 0.12111*x^2*y + 0.074299*x*y^2 + 0.16623*y^3 - 1.6423*x^2 + 0.81389*x*y - 0.40302*y^2 - 0.88487*x + 0.35337*y - 3.7906<=0".asFormula)(1) <(
        dW(1) & QE,
        //dgBarrier(1)
        sAIclosedPlus()(1) & QE
      )
    )
    println(pr)
  }
}