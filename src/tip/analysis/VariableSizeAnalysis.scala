package tip.analysis

import tip.analysis.VarSize.{VarSize, intervalToVarSizeVal}
import tip.ast.ADeclaration
import tip.ast.AstNodeData.DeclarationData
import tip.cfg._
import tip.lattices.{IntervalLattice, LiftLattice}
import tip.lattices.IntervalLattice._
import tip.solvers.WorklistFixpointSolverWithReachabilityAndWidening

object VarSize extends Enumeration {
  type VarSize = VarSizeVal

  case class VarSizeVal(interval: IntervalLattice.Element) extends super.Val
  import scala.language.implicitConversions
  implicit def intervalToVarSizeVal(interval: IntervalLattice.Element): VarSizeVal = {
    values.find {
      case VarSizeVal((vl, vh)) =>
        interval match {
          case (il, ih) => vl <= il && ih <= vh
        }
    }.get.asInstanceOf[VarSizeVal]
  }

  val Any = VarSizeVal(EmptyInterval)
  val Bool = VarSizeVal((0, 1))
  val Byte = VarSizeVal((scala.Byte.MinValue, scala.Byte.MaxValue))
  val Char = VarSizeVal((scala.Char.MinValue, scala.Char.MaxValue))
  val Int = VarSizeVal((scala.Int.MinValue, scala.Int.MaxValue))
  val BigInt = VarSizeVal(FullInterval)
}

trait VariableSizeAnalysis extends ValueAnalysisMisc with Dependencies[CfgNode] {

  import tip.cfg.CfgOps._

  val cfg: ProgramCfg

  val valuelattice: IntervalLattice.type

  val liftedstatelattice: LiftLattice[statelattice.type]

  /**
   * Int values occurring in the program, plus -infinity and +infinity.
   */
  private val B = cfg.nodes.flatMap { n =>
    n.appearingConstants.map { x =>
      IntNum(x.value): Num
    } + MInf + PInf
  }

  def loophead(n: CfgNode): Boolean = indep(n).exists(cfg.rank(_) > cfg.rank(n))

  private def minB(b: IntervalLattice.Num) = B.filter(b <= _).min

  private def maxB(a: IntervalLattice.Num) = B.filter(_ <= a).max

  def widenInterval(x: valuelattice.Element, y: valuelattice.Element): valuelattice.Element = {
    (x, y) match {
      case (IntervalLattice.EmptyInterval, _) => y
      case (_, IntervalLattice.EmptyInterval) => x
      case ((l1, h1), (l2, h2)) =>
        val a = min(Set(l1, l2))
        val b = max(Set(h1, h2))
        (maxB(a), minB(b))
    }
  }

  def widen(x: liftedstatelattice.Element, y: liftedstatelattice.Element): liftedstatelattice.Element =
    (x, y) match {
      case (liftedstatelattice.Bottom, _) => y
      case (_, liftedstatelattice.Bottom) => x
      case (liftedstatelattice.Lift(xm), liftedstatelattice.Lift(ym)) =>
        liftedstatelattice.Lift(declaredVars.map { v =>
          v -> widenInterval(xm(v), ym(v))
        }.toMap)
    }
}

object VariableSizeAnalysis {
  object Intraprocedural {
    class WorklistSolverWithWidening(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(false) {
      override def analyze(): Map[CfgNode, Map[ADeclaration, VarSize]] = {
        val impl = new WorklistSolverWithWideningImpl(cfg)
        impl.analyze().map {
          case (node, element) => node -> impl.liftedstatelattice.unlift(element).map {
            case (node, element) => node -> intervalToVarSizeVal(element)
          }
        }
      }
    }
    private class WorklistSolverWithWideningImpl(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, IntervalLattice)
        with WorklistFixpointSolverWithReachabilityAndWidening[CfgNode]
        with VariableSizeAnalysis
  }
}
