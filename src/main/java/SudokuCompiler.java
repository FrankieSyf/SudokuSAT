import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.*;

import java.io.*;
import java.util.Scanner;

public class SudokuCompiler {
    BooleanFormula[][][] unit = new BooleanFormula[9][9][9];
    /**
     * 单元格 Unit
     *
     * 行 row
     *
     * 列 col
     *
     * 宫 block
     *
     * 以上称为Region
     *      最后所有的region的clause 合取
     */

    public void initGrid(BooleanFormulaManager bmgr) {
        for (int i = 0; i < 9; i++) {
            for (int j = 0; j < 9; j++) {
                for (int k = 0; k < 9; k++) {
                    unit[i][j][k] = bmgr.makeVariable("unit" + Integer.toString(i + 1) + Integer.toString(j + 1) + Integer.toString(k + 1));
                }
            }
        }
    }

    public BooleanFormula unitClause(BooleanFormulaManager bmgr) {
        BooleanFormula temp = null, temp1 = null, temp2 = null;
        int count = 0;
        for (int i = 0; i < 9; i++) {
            for (int j = 0; j < 9; j++) {
                for (int k = 0; k < 9; k++) {
                    //!(x,y,k)∨!(x,y,m) n!=m
                    count++;
                    for (int m = k + 1; m < 9; m++) {
                        BooleanFormula a = bmgr.or(bmgr.not(unit[i][j][k]), bmgr.not(unit[i][j][m]));
                        if (k == 0 && m == 1)
                            temp = a;
                        else {
                            temp = bmgr.and(temp, a);
                        }
                    }
                }
                if (j == 0)
                    temp1 = temp;
                else temp1 = bmgr.and(temp1, temp);
            }
            if (i == 0)
                temp2 = temp1;
            else temp2 = bmgr.and(temp1, temp2);
        }
        System.out.println(count);
        return temp2;
    }

    public BooleanFormula rowClause(BooleanFormulaManager bmgr) {
        //∧x∧n∨y(x,y,n)
        //(111 121 131 141。。。191) n (112 122)
        BooleanFormula temp = null;
        BooleanFormula temp1 = null, temp2 = null;
        for (int i = 0; i < 9; i++) {
            for (int k = 0; k < 9; k++) {
                for (int j = 0; j < 9; j++) {
                    if (j == 0)
                        temp = unit[i][j][k];
                    else
                        temp = bmgr.or(temp, unit[i][j][k]);
                }
                if (k == 0)
                    temp1 = temp;
                else temp1 = bmgr.and(temp1, temp);
            }
            if (i == 0)
                temp2 = temp1;
            else temp2 = bmgr.and(temp1, temp2);
        }
        return temp2;
    }

    public BooleanFormula colClause(BooleanFormulaManager bmgr) {
        //∧y∧n∨x(x,y,n)
        BooleanFormula temp = null;
        BooleanFormula temp1 = null, temp2 = null;
        for (int j = 0; j < 9; j++) {
            for (int k = 0; k < 9; k++) {
                for (int i = 0; i < 9; i++) {
                    if (i == 0)
                        temp = unit[i][j][k];
                    else
                        temp = bmgr.or(temp, unit[i][j][k]);
                }
                if (k == 0)
                    temp1 = temp;
                else temp1 = bmgr.and(temp1, temp);
            }
            if (j == 0)
                temp2 = temp1;
            else temp2 = bmgr.and(temp1, temp2);
        }
        return temp2;
    }

    public BooleanFormula blkClause(BooleanFormulaManager bmgr) {
        //∧n∧r∧t∨i∨j(3r+i,3t+j,n)
        BooleanFormula temp = unit[0][0][0];
        BooleanFormula temp1 = null, temp2 = null, temp3 = null, temp4 = null;
        for (int k = 0; k < 9; k++) {
            for (int r = 0; r < 3; r++) {
                for (int t = 0; t < 3; t++) {
                    for (int i = 0; i < 3; i++) {
                        for (int j = 0; j < 3; j++) {
                            if (j == 0)
                                temp = unit[3 * r + i][3 * t + j][k];
                            else
                                temp = bmgr.or(temp, unit[3 * r + i][3 * t + j][k]);
                        }
                        if (i == 0)
                            temp1 = temp;
                        else temp1 = bmgr.or(temp1, temp);
                    }
                    if (t == 0)
                        temp2 = temp1;
                    else temp2 = bmgr.and(temp2, temp1);
                }
                if (r == 0)
                    temp3 = temp2;
                else temp3 = bmgr.and(temp3, temp2);
            }
            if (k == 0)
                temp4 = temp3;
            else temp4 = bmgr.and(temp3, temp4);
        }
        return temp4;
    }


    public BooleanFormula addConstraint(BooleanFormulaManager bmgr, int a, int b, int c) {
        //若已确定(a,b,c), 则row:∧y!(a,y,c) y!=b  col:∧x!(x,b,c) x!=a
        //     blk:  ∧i∧j!(3*(a/3)+i,3*(b/3)+j,c) 3*(a/3)+i!=a 3*(b/3)+j!=b
        BooleanFormula row = null;
        for (int j = 0; j < 9; j++) {
            if (j == b)
                continue;
            if (row == null) {
                row = bmgr.not(unit[a][j][c]);
                continue;
            }
            row = bmgr.and(row, bmgr.not(unit[a][j][c]));
        }
        BooleanFormula col = null;
        for (int i = 0; i < 9; i++) {
            if (i == a)
                continue;
            if (col == null) {
                col = bmgr.not(unit[i][b][c]);
                continue;
            }
            col = bmgr.and(col, bmgr.not(unit[i][b][c]));
        }

        BooleanFormula blk = null;
        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 3; j++) {
                if (3 * (a / 3) + i != a || 3 * (b / 3) + j != b) {
                    if (blk == null) {
                        blk = bmgr.not(unit[3 * (a / 3) + i][3 * (b / 3) + j][c]);
                        continue;
                    }
                    blk = bmgr.and(blk, bmgr.not(unit[3 * (a / 3) + i][3 * (b / 3) + j][c]));
                }
            }
        }
        return bmgr.and(unit[a][b][c], row, col, blk);
    }

    public static void main(String[] args) throws InvalidConfigurationException, InterruptedException, IOException {
        Configuration config = Configuration.fromCmdLineArguments(args);
        LogManager logger = BasicLogManager.create(config);
        ShutdownManager shutdown = ShutdownManager.create();


        SolverContext context = SolverContextFactory.createSolverContext(
                config, logger, shutdown.getNotifier(), SolverContextFactory.Solvers.SMTINTERPOL);

        FormulaManager fmgr = context.getFormulaManager();
        BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();

        SudokuCompiler sudokuCompiler = new SudokuCompiler();
        sudokuCompiler.initGrid(bmgr);

        String file = "/Users/xx/Desktop/SudokuSAT/src/main/test.txt";

        Scanner scanner = new Scanner(new File(file));
        BooleanFormula randomConstraint = bmgr.makeVariable("ran");
        while (scanner.hasNextLine()) {
            String s = scanner.nextLine();
            int a = s.charAt(1) - '0' - 1;
            int b = s.charAt(3) - '0' - 1;
            int c = s.charAt(5) - '0' - 1;
            randomConstraint = bmgr.and(randomConstraint, sudokuCompiler.addConstraint(bmgr, a, b, c));
        }

        BooleanFormula constraint = bmgr.and(sudokuCompiler.unitClause(bmgr),sudokuCompiler.rowClause(bmgr),
                sudokuCompiler.colClause(bmgr),sudokuCompiler.blkClause(bmgr),randomConstraint);

        try (ProverEnvironment prover = context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
            prover.addConstraint(constraint);
            boolean isUnsat = prover.isUnsat();
            System.out.println("SAT?" + !isUnsat);
            if (!isUnsat) {
                Model model = prover.getModel();
                for (int i = 0; i < 9; i++) {
                    for (int j = 0; j < 9; j++) {
                        for (int k = 0; k < 9; k++) {
                            Boolean value = model.evaluate(sudokuCompiler.unit[i][j][k]);
                            if (value) {
//                                System.out.println(sudokuCompiler.unit[i][j][k] + " " + value);
                                System.out.print((k+1)+" ");
                                if (j==8)
                                    System.out.println();
                            }
                        }
                    }
                }
            }
        } catch (SolverException e) {
            e.printStackTrace();
        }

    }
}
