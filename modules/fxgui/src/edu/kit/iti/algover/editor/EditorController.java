package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.util.ImmutableList;
import javafx.collections.ListChangeListener;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import org.antlr.runtime.Token;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
// TODO: Implement saving files / updating files when they change on disk
public class EditorController {

    private final TabPane view;
    private final Map<DafnyFile, Tab> tabsByFile;

    public EditorController() {
        this.view = new TabPane();
        this.tabsByFile = new HashMap<>();
        view.getTabs().addListener(this::onTabListChanges);
    }

    private void onTabListChanges(ListChangeListener.Change<? extends Tab> change) {
        while (change.next()) {
            if (change.wasRemoved()) {
                for (Tab removedTab : change.getRemoved()) {
                    tabsByFile.remove(removedTab.getUserData());
                }
            }
        }
    }

    public void viewFile(DafnyFile dafnyFile) {
        Tab existingTab = tabsByFile.get(dafnyFile);
        if (existingTab != null) {
            view.getSelectionModel().select(existingTab);
        } else {
            try {
                String contentAsText = fileToString(dafnyFile.getRepresentation().getFilename());
                Tab tab = new Tab();
                tab.setText(dafnyFile.getFilename());
                tab.setUserData(dafnyFile);
                tab.setContent(new DafnyCodeArea(contentAsText));
                tabsByFile.put(dafnyFile, tab);
                view.getTabs().add(tab);
                view.getSelectionModel().select(tab);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private DafnyCodeArea getFocusedCodeArea() {
        return (DafnyCodeArea) view.getSelectionModel().getSelectedItem().getContent();
    }

    public void viewPVCSelection(PVC pvc) {
        DafnyCodeArea codeArea = getFocusedCodeArea();

        SymbexPath symbexPath = pvc.getPathThroughProgram();

        List<DafnyTree> assignmentsAsList = new ArrayList<>();
        symbexPath.getAssignmentHistory().forEach(assignmentsAsList::add);
        List<Token> assignmentTokens =
            assignmentsAsList.stream()
                .flatMap(dafnyTree -> collectTokens(dafnyTree).stream())
                .collect(Collectors.toList());

        List<PathConditionElement> pathConditionsAsList = new ArrayList<>();
        symbexPath.getPathConditions().forEach(pathConditionsAsList::add);

        List<Token> positiveGuardTokens = pathConditionsAsList.stream()
            .filter(pathConditionElement -> pathConditionElement.getType() == PathConditionElement.AssumptionType.IF_THEN)
            .flatMap(pathConditionElement -> collectTokens(pathConditionElement.getExpression()).stream())
            .collect(Collectors.toList());

        List<Token> negativeGuardTokens = pathConditionsAsList.stream()
            .filter(pathConditionElement -> pathConditionElement.getType() == PathConditionElement.AssumptionType.IF_ELSE)
            .flatMap(pathConditionElement -> collectTokens(pathConditionElement.getExpression()).stream())
            .collect(Collectors.toList());

        List<Token> allGuardTokens = pathConditionsAsList.stream()
            .flatMap(pathConditionElement -> collectTokens(pathConditionElement.getExpression()).stream())
            .collect(Collectors.toList());

        List<AssertionElement> proofObligationsAsList = new ArrayList<>();
        symbexPath.getProofObligations().forEach(proofObligationsAsList::add);
        List<Token> proofObligationTokens = proofObligationsAsList.stream()
            .flatMap(assertionElement -> collectTokens(assertionElement.getOrigin()).stream())
            .collect(Collectors.toList());

        // TODO: Find out what the tokens are for a method header. for example for the header
        // "method max(x: int, y: int) returns (m: int) {". That should still be highlighted

        codeArea.setHighlightingRule((token, syntaxClasses) -> {
            if (oneTokenMatches(assignmentTokens, token)) {
                return syntaxClasses;
            } else if (oneTokenMatches(proofObligationTokens, token)) {
                return syntaxClasses;
            } else if (oneTokenMatches(allGuardTokens, token)) {
                if (oneTokenMatches(positiveGuardTokens, token)) {
                    return addClass(syntaxClasses, "guard-positive");
                } else if (oneTokenMatches(negativeGuardTokens, token)) {
                    return addClass(syntaxClasses, "guard-negative");
                } else {
                    return syntaxClasses;
                }
            } else {
                return Collections.singletonList("lowlighted");
            }
        });
        codeArea.rerenderHighlighting();
    }

    private Collection<String> addClass(Collection<String> syntaxClasses, String cssClass) {
        List<String> classes = new ArrayList<>();
        classes.addAll(syntaxClasses);
        classes.add(cssClass);
        return classes;
    }

    private boolean oneTokenMatches(List<Token> tokens, Token token) {
        return tokens.stream().anyMatch(specificToken -> tokensMatch(specificToken, token));
    }

    private boolean tokensMatch(Token asgnToken, Token token) {
        return asgnToken.getLine() == token.getLine() && asgnToken.getCharPositionInLine() == token.getCharPositionInLine();
    }

    public void resetPVCSelection() {
        DafnyCodeArea codeArea = getFocusedCodeArea();
        codeArea.setHighlightingRule(null);
        codeArea.rerenderHighlighting();
    }

    private List<Token> collectTokens(DafnyTree tree) {
        List<Token> tokens = new ArrayList<>();
        collectTokensTo(tokens, tree);
        return tokens;
    }

    private void collectTokensTo(List<Token> list, DafnyTree tree) {
        list.add(tree.getToken());
        tree.getChildren().forEach(subTree -> collectTokensTo(list, subTree));
    }

    public TabPane getView() {
        return view;
    }

    private static String fileToString(String filename) throws IOException {
        Path path = FileSystems.getDefault().getPath(filename);
        return new String(Files.readAllBytes(path));
    }
}
