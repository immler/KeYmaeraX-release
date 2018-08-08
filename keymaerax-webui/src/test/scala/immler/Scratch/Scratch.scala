package immler.Scratch
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import org.apache.logging.log4j.scala.Logger
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.useAt
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.derivedAxiom
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{useAt, _}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import scala.language.postfixOps
import scala.collection.immutable.{List, _}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper.{simpWithTool, stripConstants}

import scala.collection.immutable._

class Scratch extends TacticTestBase {

  private val logger = Logger(getClass)
  
  def summands(t: Term): List[Term] = t match {
    case t: Plus => t.right::summands(t.left)
    case x: Term => List(x)
  }

  def factors(t: Term): List[Term] = t match {
    case t: Times => t.right::factors(t.left)
    case x: Term => List(x)
  }

  def power(t: Term) = t match {
    case t: Power => t.right match {
      case n: Number => n.value
    }
  }

  /* of a monomial */
  def order(t: Term) = t match {
    case t: Times => ((factors(t.right).dropRight(1)) map power) sum
  }

  def normalise(p: Term) = {
    PolynomialArith.normalise(p, true)._1
  }

  def normalizedLieDerivative(p: DifferentialProgram, t: Term): Term = {
    val ld = DifferentialHelper.simplifiedLieDerivative(p,t, ToolProvider.simplifierTool())
    normalise(ld)
  }

  def normalizedLieDerivatives(p: DifferentialProgram, ts: List[Term]): List[Term] =
    ts map (t => normalizedLieDerivative(p, t))

  def sum(ts: List[Term]) = if (ts isEmpty) Number(0) else ts.reduce (Plus(_, _))

  /* a polynomial in normal form */
  def truncate(t: Term, k: Int): Term = {
    val ss = summands(t).dropRight(1) filter (t => order(t) <= k)
    sum(ss)
  }

  def truncates(ts: List[Term], k: Int): List[Term] = ts map (t => truncate(t, k))

  def truncHigherLieDerivatives(p: DifferentialProgram, ts: List[Term], i: Int, k: Int): List[Term] = {
    if (i==0) ts
    else {
      val r = truncHigherLieDerivatives(p, ts, i - 1, k + 1)
      val l = normalizedLieDerivatives(p, r)
      val res = truncates(l, k)
      res.map (r => simpWithTool(ToolProvider.simplifierTool(), r))
    }
  }

  def factorial(n: Int) = List.range(1, n+1).product

  def TaylorModel(p: DifferentialProgram, state: List[Variable], time: Variable, k: Int): List[Term] = {
    val tool = ToolProvider.simplifierTool()
    val terms = (0 to k).toList.map { i =>
      truncHigherLieDerivatives(p, state, i, k - i).map { t =>
        val m = Times(t, Divide(Power(time, Number(i)), Number(factorial(i))))
        simpWithTool(tool, m)
      }
    }
    terms.transpose.map (t => stripConstants(sum(t)))
  }

  def equalTo (fml1: Term, fml2: Term): Boolean =
    proveBy(Equal(fml1,fml2), QE()).subgoals.isEmpty

  "Taylor models" should "be computed correctly" in withMathematica { _ =>
    val ode = "{x' = 1 + y, y' = - x^2, t' = 1}".asDifferentialProgram
    val tm4 = TaylorModel(ode, List("x", "y").map (s=>s.asVariable), "t".asVariable, 4)
    val tm3 = TaylorModel(ode, List("x", "y").map (s=>s.asVariable), "t".asVariable, 3)
    val tm2 = TaylorModel(ode, List("x", "y").map (s=>s.asVariable), "t".asVariable, 2)
    val tm1 = TaylorModel(ode, List("x", "y").map (s=>s.asVariable), "t".asVariable, 1)
    equalTo (tm4(0), "x + t + t*y - 1/2*t^2*x^2 - 1/3*t^3*x-1/12*t^4".asTerm) shouldBe true
    equalTo (tm4(1), "y - t*x^2 - t^2*x - t^2*x*y - 1/3*t^3 - 2/3*t^3*y".asTerm) shouldBe true

    equalTo (tm3(0), "x + t + t*y ".asTerm) shouldBe true
    equalTo (tm3(1), "y - t*x^2 - t^2*x - 1/3*t^3".asTerm) shouldBe true

    equalTo (tm2(0), "x + t + t*y".asTerm) shouldBe true
    equalTo (tm2(1), "y".asTerm) shouldBe true

    equalTo (tm1(0), "x + t".asTerm) shouldBe true
    equalTo (tm1(1), "y".asTerm) shouldBe true
  }

  "Taylor Model precondition" should "be proved" in withMathematica { _ =>
    val x = (
      "(" +
        " -1 <= x0 & x0 <= 1 &" +
        "-0.5 <= y0 & y0 <= 0.5 &" +
        "h = 0.02 & e = 0.000000000001 &" +
        "ex = 0.0005 &" +
        "ey = 0.0005" +
        ")" +
        " ->" +
        "(" +
        "ex>0 & ey>0 & e>0 & h>0 &" +
        "(\\forall t \\forall x \\forall y" +
        "(" +
        "(0<=t&t<=h&x-ex*t/h-e < x0+t+t*y0&x0+t+t*y0 < x+ex*t/h+e&y-ey*(t/h)-e < y0-x0^2*t-x0*t^2-t^3/3&y0-x0^2*t-x0*t^2-t^3/3 < y+ey*(t/h)+e)" +
        "->" +
        "(1+y-ex*h/h^2<=1+y0&1+y0<=1+y+ex*h/h^2&-x^2-ey*(h/h^2)<=-x0^2-x0*(2*t)-3*t^2*3/9&-x0^2-x0*(2*t)-3*t^2*3/9<=-x^2+ey*(h/h^2))" +
        ")" +
        ")" +
        ")").asFormula
    val result = proveBy(x, QE())
    result.subgoals should have size 0
  }

  def getTime(ode: DifferentialProgram): Variable = {
    val aodes = DifferentialHelper.atomicOdes(ode)
    aodes find (_.e == Number(1)) match {
      case Some(aode) => aode.xp.x
      case None => throw new IllegalArgumentException("getTime: no time variable in ode")
    }
  }

  def substitutes(xs: List[(Term, Term)])(t: Term) =
      xs.foldLeft(t) ((t, x) => SubstitutionHelper.replaceFree(t)(x._1, x._2))

  def createTaylorModelLemma(ode: DifferentialProgram, order: Int) = {
    val time = getTime(ode)
    val vars = DifferentialHelper.getPrimedVariables(ode)
    val state = vars.filterNot(_ == time)
    def const(n: String) = FuncOf(Function(n + "_", None, Unit, Real), Nothing)
    val istate = vars map (x => const(x.name + "0")) // TODO: should be fresh?!
    val tm = TaylorModel(ode, state, time, order)
    val tm0 = tm map (substitutes (state zip state))

    val open_bound = const("e") // TODO: should be fresh!
    val step_size = const("h") // TODO: should be fresh!
    val indices = 0 until state.length toList
    val ivl_vars = indices map (n => const("i"+n)) // TODO: should be fresh!

    def bound(i: Int): List[Formula] = {
      val tdi = Plus(Times(Divide(time, step_size), ivl_vars(i)), open_bound)
      List(Less(Minus(tm0(i), tdi), vars(i)),
        Less(vars(i), Plus(tm0(i), tdi)))
    }

    val bounds = (indices flatMap bound) reduceRight And
    val pos_preconds = (open_bound::step_size::ivl_vars) map (Less (Number(0), _): Formula)
    val initial_condition = Equal(time,Number(0))::(state zip istate map (x => Equal(x._1, x._2)))
    def mk_stmt(assms: List[Formula]) =
      Imply((pos_preconds:::initial_condition:::assms) reduceRight And, Box(ODESystem(ode, And(LessEqual(Number(0), time), LessEqual(time, step_size))),bounds))
    logger.debug(mk_stmt(Nil))
    val res = proveBy(mk_stmt(Nil),
      implyR(1)
        & useAt("DIo open differential invariance <" + (state.size * 2).toString)(1)
        & andR(1)
        & Idioms.<(testb(1) & QE(),
          implyR(1)
            & DE(1) & skip
            & derive(Position(1)++PosInExpr(List.fill(state.size + 1 /*time*/ + 1 /*program*/ + 1 /*implication*/)(1)))
            & SaturateTactic(Dassignb(Position(1)++PosInExpr(1::Nil)))
            & dW(1)
            & SimplifierV2.fullSimpTac
      ))
    def quantify(vars: List[Variable], fm: Formula) = vars.foldRight(fm)((x, fm) => Forall(x::Nil, fm))
    val assumption = quantify(time::state, res.subgoals(0).succ(0))
    
    logger.debug("x")
    logger.debug(assumption)
    logger.debug("-x")
    val proved = proveBy(mk_stmt(assumption::Nil),
        implyR(1)
          & useAt("DIo open differential invariance <" + (state.size * 2).toString)(1)
          & andR(1)
          & Idioms.<(testb(1) & QE(),
          implyR(1)
            & DE(1) & skip
            & derive(Position(1)++PosInExpr(List.fill(state.size + 1 /*time*/ + 1 /*program*/ + 1 /*implication*/)(1)))
            & SaturateTactic(Dassignb(Position(1)++PosInExpr(1::Nil)))
            & dW(1)
            & SimplifierV2.fullSimpTac
            & QE()
        ))

    // see Lemma.scala, also for storing Lemmas in the Database
    // (probably I don't want this, rather locally, for some TM cache in several steps?)
    val evidence = ToolEvidence(("input",proved.toString)::("output", "true")::Nil)::Nil
    Lemma(proved, evidence, None)
  }

  /*
  * P(x) -> (\forall x (Q(x) -> [{{x'=f(x) & Q(x)}}*]P(x))) -> [{x'=f(x) & Q(x)}]P(x)
  * P(x) -> (\forall x (Q(x) -> [{{x'=f(x) & Q(x)}}]P(x))) -> [{x'=f(x) & Q(x)}]P(x)
  * P(x) -> [{{x'=f(x) & Q(x)}; {x'=f(x) & Q(x)}}]P(x) -> [{x'=f(x) & Q(x)}]P(x)
  * [{{x'=f(x) & Q(x) & (J(x))}; ?J(x); {x' = f(x) & Q(x)}}]P(x) -> [{x'=f(x) & Q(x)}]P(x)
  *
  * [{x'=f(x) & Q(x)}]P(x) -> [{x'=f(x) & Q(x)}]P(x)
  * [{x'=f(x) & Q(x)}][{{x'=f(x) & Q(x)}}*]P(x) -> [{x'=f(x) & Q(x)}]P(x)
  *
  * IDEE: prepend cut invariant R and jump condition J :
  * P(x) -> [{{x'=f(x) & Q(x) & R(x)}; ?J(x);}][{{x'=f(x) & Q(x)}}]P(x) -> [{x'=f(x) & Q(x)}]P(x)
  * */
  def cutTaylorModelTac(): BelleExpr = skip

/*
* Scratch: [{x'=f(x),t'=1&true}]P((t,x)) <->
*       [{{x'=f(x),t'=1 & true};?(0<=t&t<=h)}++{{x'=f(x),t'=1 & true};?(t>=h)}]P((t,x))
*       [{{x'=f(x),t'=1 & true};?(0<=t&t<=h);}++{{x'=f(x),t'=1 & true};?(t>=h);}]P((t,x))
*       [{{x'=f(x),t'=1 & true}}++{{x'=f(x),t'=1 & true}}]P((t,x))
*       [{x'=f(x),t'=1&t>=0}]P((t,x))<->[{x'=f(x),t'=1&t>=0}?0<=t&t<=h;++{x'=f(x),t'=1&t>=0}?t>=h;]P((t,x))
*
*     [{{x'=f(x),t'=1 &t>=0}; ?((0<=t&t<=h)|t>=h);}]P((t,x))
*
*     [{{x'=f(x),t'=1 &t>=0} {?(t<=h)++{?(t=h); {x'=f(x),t'=1 &t>=0}}}]P((t,x))
*
*     [{{x'=f(x),t'=1 &t>=0} {?(t<=h);++{?(t=h); {x'=f(x),t'=1 &t>=0}}}}]P((t,x))
*     [{{x'=f(x),t'=1 &true} {x'=f(x),t'=1 &true}]P((t,x))
* */

  def odeStep(fml: Formula) = NamedTactic("ANON",
      useAt(DerivedAxioms.loopApproxb, PosInExpr(1::Nil))(1)
    & iterateb(1)
    & andR(1) & Idioms.<(skip /* precondition 1, left to user */,
        dC(fml)(1))
  )

  "Lemma" should "be tried" in {
    val flow = "[{x' = 1 + y, y' = - x^2, t' = 1 & D(x, y, t)}]P(x, y, t)".asFormula
    val step = "0<=t & t <= h".asFormula

    val result = proveBy(flow, odeStep(step))
    logger.debug(result)

    val result2 = proveBy(("[{x' = 1 + y, y' = - x^2, t' = 1 & D(x, y, t)} ?t>=h;]P(x, y, t) <- [{x' = 1 + y, y' = - x^2, t' = 1 & D(x, y, t)} ?t=h; {x' = 1 + y, y' = - x^2, t' = 1 & D(x, y, t)}]P(x, y, t)").asFormula,
      skip)
    logger.debug(result2)

  }


  "Taylor model" should "be cut" in withMathematica { _ =>
    val result = proveBy("[{x' = 1 + y, y' = - x^2, t' = 1}]P(x, y, t)".asFormula, cutTaylorModelTac())
    val x = "[{{x'=f(x),t'=1 &t>=0} {?(t<=h);++{?(t=h); {x'=f(x),t'=1 &t>=0}}}}]P((t,x))".asFormula
    /* Step 1: do a step!
    * Try this as a cut: t=0->([{{x'=f(x),t'=1}}]P(t, x)<->(([{{x'=f(x),t'=1}}](0<=t&t<=h->P(t, x)))& ((t=h&P(t, x))-> ([{{x'=f(x),t'=1}}]P(t, x)))))
    *
    * [expr]P(t) <->
    * [ode]P(t) <-> ([ode](0<=t<=h -> P(t)) & ((t = h & P h) -> [ode](t > h -> P(t))))
    *               ([ode&0<=t<=h]P(t)) &
    * P for unbounded time <-> [ode](0<=t<=h -> P t) & [ode](t > h -> P t)
    * */
    logger.debug(result)
  }

  "Taylor model lemma" should "be created" in withMathematica { _ =>
    val lemma = createTaylorModelLemma("{x' = 1 + y, y' = - x^2, t' = 1}".asDifferentialProgram, 1)
    val lemmaDB = LemmaDBFactory.lemmaDB
    val lemmaID = lemmaDB.add(lemma)
    lemmaID
    logger.debug(lemmaID)
    val lemmaFact = LemmaDBFactory.lemmaDB.get(lemmaID).get.fact
    logger.debug(lemmaFact)
    // use a lemma literally
    TactixLibrary.by(lemmaFact)
    // use a uniform substitution instance of a lemma
    TactixLibrary.byUS(lemmaFact)

    //

  }

}