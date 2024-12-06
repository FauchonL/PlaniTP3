package fr.uga.pddl4j.examples.asp;

import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.parser.RequireKey;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.problem.DefaultProblem;
import fr.uga.pddl4j.problem.Fluent;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.util.BitVector;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.*;
import picocli.CommandLine;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.InvalidPathException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;


@CommandLine.Command(name = "SAT2", version = "SAT2 1.0", description = "Résoudre un problème avec un planner SAT.", sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", parameterListHeading = "%nParameters:%n", optionListHeading = "%nOptions:%n")
public class SATsolver extends AbstractPlanner {

    private static final Logger LOGGER = LogManager.getLogger(SATsolver.class.getName());
    private int sizePlan = 1;

    
    public static void main(String[] args) {

        try {
            final SATsolver planner = new SATsolver();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }

    @Override
    public Problem instantiate(DefaultParsedProblem problem) {
        final Problem pb = new DefaultProblem(problem);
        pb.instantiate();
        return pb;
    }

  
    public int getFluentID(Problem problem, Fluent state, int timeStep) {
        int idxState = problem.getFluents().indexOf(state);
        return (problem.getFluents().size() + problem.getActions().size()) * timeStep + 1 + idxState;
    }

    
    public int getActionID(Problem problem, Action action, int timeStep) {
        int idxAction = problem.getActions().indexOf(action);
        return (problem.getFluents().size() + problem.getActions().size()) * timeStep + 1 + problem.getFluents().size()
                + idxAction;
    }

    public Action getActionIndex(Problem problem, int actionUniqueID) {

        if (actionUniqueID <= 0) {
            return null;
        }

        int idx = (actionUniqueID - 1) % (problem.getFluents().size() + problem.getActions().size());

        if (idx >= problem.getFluents().size()) {
            return problem.getActions().get(idx - problem.getFluents().size());
        } else {
            return null;
        }
    }

    public Vec<IVecInt> encodeInitState(final Problem problem, int planSize) {

        Vec<IVecInt> clausesInitState = new Vec<IVecInt>();

        BitVector initStatePosFluents = problem.getInitialState().getPositiveFluents();

        HashSet<Integer> fluentsNotInInitState = new HashSet<Integer>();
        for (int i = 0; i < problem.getFluents().size(); i++) {
            fluentsNotInInitState.add(i);
        }

        for (int p = initStatePosFluents.nextSetBit(0); p >= 0; p = initStatePosFluents.nextSetBit(p + 1)) {
            Fluent f = problem.getFluents().get(p);

            fluentsNotInInitState.remove(p);

            int idxFluent = getFluentID(problem, f, 0);
            VecInt clause = new VecInt(new int[]{idxFluent});
            clausesInitState.push(clause);

            initStatePosFluents.set(p);
        }

        for (Integer stateNotInInitState : fluentsNotInInitState) {
            VecInt clause = new VecInt(new int[]{-(stateNotInInitState + 1)});
            clausesInitState.push(clause);
        }

        LOGGER.debug("Clause init state: {}\n", clausesInitState);

        return clausesInitState;
    }

    public Vec<IVecInt> encodeFinState(final Problem problem, int planSize) {

        Vec<IVecInt> clausesGoalState = new Vec<IVecInt>();

        BitVector goalPosFluents = problem.getGoal().getPositiveFluents();

        for (int p = goalPosFluents.nextSetBit(0); p >= 0; p = goalPosFluents.nextSetBit(p + 1)) {
            Fluent f = problem.getFluents().get(p);

            int idxFluent = getFluentID(problem, f, planSize);
            VecInt clause = new VecInt(new int[]{idxFluent});
            clausesGoalState.push(clause);

            goalPosFluents.set(p);
        }

        return clausesGoalState;
    }


    public Vec<IVecInt> encodeActions(final Problem problem, int planSize) {

        Vec<IVecInt> clausesActions = new Vec<IVecInt>();

        Fluent f;

        for (int timeStep = 0; timeStep < planSize; timeStep++) {
            for (Action action : problem.getActions()) {

                int actionUniqueIDforTimeStep = getActionID(problem, action, timeStep); 

                // Obtneir les preconditions et les effets de l'action
                BitVector precondPos = action.getPrecondition().getPositiveFluents();
                for (int p = precondPos.nextSetBit(0); p >= 0; p = precondPos.nextSetBit(p + 1)) {
                    f = problem.getFluents().get(p);

                    int fluentUniqueIDforTimeStep = getFluentID(problem, f, timeStep);
                    VecInt clause = new VecInt(new int[]{-actionUniqueIDforTimeStep, fluentUniqueIDforTimeStep});
                    clausesActions.push(clause);
                    precondPos.set(p);
                }

                BitVector precondNeg = action.getPrecondition().getNegativeFluents();
                for (int p = precondNeg.nextSetBit(0); p >= 0; p = precondNeg.nextSetBit(p + 1)) {
                    f = problem.getFluents().get(p);

                    int idxFluent = getFluentID(problem, f, timeStep);
                    VecInt clause = new VecInt(new int[]{-actionUniqueIDforTimeStep, -idxFluent});
                    clausesActions.push(clause);
                    precondNeg.set(p);
                }

                BitVector effectPos = action.getUnconditionalEffect().getPositiveFluents();
                for (int p = effectPos.nextSetBit(0); p >= 0; p = effectPos.nextSetBit(p + 1)) {
                    f = problem.getFluents().get(p);

                    int idxFluent = getFluentID(problem, f, timeStep + 1);
                    VecInt clause = new VecInt(new int[]{-actionUniqueIDforTimeStep, idxFluent});
                    clausesActions.push(clause);

                    effectPos.set(p);
                }

                BitVector effectNeg = action.getUnconditionalEffect().getNegativeFluents();
                for (int p = effectNeg.nextSetBit(0); p >= 0; p = effectNeg.nextSetBit(p + 1)) {
                    f = problem.getFluents().get(p);

                    int idxFluent = getFluentID(problem, f, timeStep + 1);
                    VecInt clause = new VecInt(new int[]{-actionUniqueIDforTimeStep, -idxFluent});
                    clausesActions.push(clause);

                    effectNeg.set(p);
                }
            }
        }

        LOGGER.debug("Clauses action: {}\n", clausesActions);

        return clausesActions;
    }

    
    public Vec<IVecInt> encodeExplanatoryFrameAxioms(final Problem problem, int planSize) {

        Vec<IVecInt> clausesExplanatoryFrameAxioms = new Vec<IVecInt>();

        ArrayList<Action>[] positiveEffectOnFluent = (ArrayList<Action>[]) new ArrayList[problem.getFluents().size()];
        ArrayList<Action>[] negativeEffectOnFluent = (ArrayList<Action>[]) new ArrayList[problem.getFluents().size()];

        for (int i = 0; i < problem.getFluents().size(); i++) {
            positiveEffectOnFluent[i] = new ArrayList<Action>();
            negativeEffectOnFluent[i] = new ArrayList<Action>();
        }

        for (Action action : problem.getActions()) {
            BitVector effectPos = action.getUnconditionalEffect().getPositiveFluents();

            for (int p = effectPos.nextSetBit(0); p >= 0; p = effectPos.nextSetBit(p + 1)) {
                positiveEffectOnFluent[p].add(action);
                effectPos.set(p);
            }

            BitVector effectNeg = action.getUnconditionalEffect().getNegativeFluents();

            for (int p = effectNeg.nextSetBit(0); p >= 0; p = effectNeg.nextSetBit(p + 1)) {
                negativeEffectOnFluent[p].add(action);
                effectNeg.set(p);
            }
        }

        for (int stateIdx = 0; stateIdx < problem.getFluents().size(); stateIdx++) {
            for (int timeStep = 0; timeStep < planSize; timeStep++) {
                if (positiveEffectOnFluent[stateIdx].size() != 0) {

                    Fluent f = problem.getFluents().get(stateIdx);
                    VecInt clause = new VecInt();

                    clause.push(getFluentID(problem, f, timeStep));
                    clause.push(-getFluentID(problem, f, timeStep + 1));

                    for (Action action : positiveEffectOnFluent[stateIdx]) {
                        clause.push(getActionID(problem, action, timeStep));
                    }

                    clausesExplanatoryFrameAxioms.push(clause);
                }

                if (negativeEffectOnFluent[stateIdx].size() != 0) {

                    Fluent f = problem.getFluents().get(stateIdx);
                    VecInt clause = new VecInt();

                    clause.push(-getFluentID(problem, f, timeStep));
                    clause.push(getFluentID(problem, f, timeStep + 1));

                    for (Action action : negativeEffectOnFluent[stateIdx]) {
                        clause.push(getActionID(problem, action, timeStep));
                    }

                    clausesExplanatoryFrameAxioms.push(clause);
                }
            }
        }

        return clausesExplanatoryFrameAxioms;
    }

    
    public Vec<IVecInt> encodeCompleteExclusionAxioms(final Problem problem, int planSize) {

        Vec<IVecInt> clausesCompleteExclusionAxioms = new Vec<IVecInt>();

        for (int iteratorAction1 = 0; iteratorAction1 < problem.getActions().size(); iteratorAction1++) {
            for (int iteratorAction2 = 0; iteratorAction2 < iteratorAction1; iteratorAction2++) {

                Action action1 = problem.getActions().get(iteratorAction1);
                Action action2 = problem.getActions().get(iteratorAction2);

                int initAction1Idx = getActionID(problem, action1, 0);
                int initAction2Idx = getActionID(problem, action2, 0);

                int offsetToNextActionIdx = problem.getActions().size() + problem.getFluents().size();

                for (int timeStep = 0; timeStep < planSize; timeStep++) {

                    int offset = offsetToNextActionIdx * timeStep;
                    VecInt clause = new VecInt(
                            new int[]{-(initAction1Idx + offset),
                                    -(initAction2Idx + offset)});
                    clausesCompleteExclusionAxioms.push(clause);
                }
            }
        }

        return clausesCompleteExclusionAxioms;
    }

    public int[] solve(Vec<IVecInt> allClauses, Problem problem) throws TimeoutException {
        final int MAXVAR = (problem.getFluents().size() + problem.getActions().size()) * this.sizePlan
                + problem.getFluents().size();

        ISolver solver = SolverFactory.newDefault();

        solver.newVar(MAXVAR);
        solver.setExpectedNumberOfClauses(allClauses.size());

        try {
            solver.addAllClauses(allClauses);
        } catch (ContradictionException e) {
            return null;
        }

        IProblem problemSAT = solver;
        try {
            if (problemSAT.isSatisfiable()) {
                return problemSAT.model();

            } else {
                return null;
            }
        } catch (TimeoutException e) {
            LOGGER.error("Timeout !\n");
            throw new TimeoutException("Timeout to find a model for the problem");
        }
    }

    public Vec<IVecInt> encodeProblemAsCNF(Problem problem, int planSize) {
        Vec<IVecInt> clausesInitState = encodeInitState(problem, planSize);
        Vec<IVecInt> clausesGoalState = encodeFinState(problem, planSize);
        Vec<IVecInt> clausesActions = encodeActions(problem, planSize);
        Vec<IVecInt> clausesExplanatoryFrameAxioms = encodeExplanatoryFrameAxioms(problem, planSize);
        Vec<IVecInt> clausesCompleteExclusionAxioms = encodeCompleteExclusionAxioms(problem, planSize);

        Vec<IVecInt> allClauses = new Vec<IVecInt>(clausesInitState.size() + clausesGoalState.size()
                + clausesActions.size() + clausesExplanatoryFrameAxioms.size() + clausesCompleteExclusionAxioms.size());
        clausesInitState.copyTo(allClauses);
        clausesGoalState.copyTo(allClauses);
        clausesActions.copyTo(allClauses);
        clausesExplanatoryFrameAxioms.copyTo(allClauses);
        clausesCompleteExclusionAxioms.copyTo(allClauses);

        return allClauses;
    }

    public Plan constructPlanFromModel(int[] model, Problem problem) {
        Plan plan = new SequentialPlan();
        int idxActionInPlan = 0;
        for (Integer idx : model) {
            Action a = getActionIndex(problem, idx);
            if (a != null) {
                // prettyPrintAction(a, problem);
                plan.add(idxActionInPlan, a);
                idxActionInPlan++;
            }
        }
        return plan;
    }

    @Override
    public Plan solve(final Problem problem) {

        int[] model;

        while (true) {

            final long beginEncodeTime = System.currentTimeMillis();
            Vec<IVecInt> allClauses = encodeProblemAsCNF(problem, this.sizePlan);
            final long endEncodeTime = System.currentTimeMillis();
            this.getStatistics()
                    .setTimeToEncode(this.getStatistics().getTimeToEncode() + (endEncodeTime - beginEncodeTime));

            final long beginSolveTime = System.currentTimeMillis();
            try {
                model = solve(allClauses, problem);
            } catch (TimeoutException e) {
                final long endSolveTime = System.currentTimeMillis();
                this.getStatistics()
                        .setTimeToSearch(this.getStatistics().getTimeToSearch() + endSolveTime - beginSolveTime);
                return null;
            }

            final long endSolveTime = System.currentTimeMillis();
            this.getStatistics()
                    .setTimeToSearch(this.getStatistics().getTimeToSearch() + endSolveTime - beginSolveTime);

            if (model == null) {
                this.sizePlan *= 2;
            } else {
                break;
            }
        }

        Plan plan = constructPlanFromModel(model, problem);

        return plan;
    }

    @Override
    public boolean isSupported(Problem problem) {
        return !problem.getRequirements().contains(RequireKey.ACTION_COSTS)
                && !problem.getRequirements().contains(RequireKey.CONSTRAINTS)
                && !problem.getRequirements().contains(RequireKey.CONTINOUS_EFFECTS)
                && !problem.getRequirements().contains(RequireKey.DERIVED_PREDICATES)
                && !problem.getRequirements().contains(RequireKey.DURATIVE_ACTIONS)
                && !problem.getRequirements().contains(RequireKey.DURATION_INEQUALITIES)
                && !problem.getRequirements().contains(RequireKey.FLUENTS)
                && !problem.getRequirements().contains(RequireKey.GOAL_UTILITIES)
                && !problem.getRequirements().contains(RequireKey.METHOD_CONSTRAINTS)
                && !problem.getRequirements().contains(RequireKey.NUMERIC_FLUENTS)
                && !problem.getRequirements().contains(RequireKey.OBJECT_FLUENTS)
                && !problem.getRequirements().contains(RequireKey.PREFERENCES)
                && !problem.getRequirements().contains(RequireKey.TIMED_INITIAL_LITERALS)
                && !problem.getRequirements().contains(RequireKey.HIERARCHY);
    }
}
