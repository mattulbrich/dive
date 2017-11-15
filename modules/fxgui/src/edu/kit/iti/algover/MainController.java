package edu.kit.iti.algover;

import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.browser.entities.PVCGetterVisitor;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.CodeReference;
import edu.kit.iti.algover.references.GetReferenceTypeVisitor;
import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.references.Reference;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.SequentActionListener;
import edu.kit.iti.algover.sequent.SequentController;
import edu.kit.iti.algover.timeline.TimelineLayout;

import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ExecutorService;

/**
 * Created by philipp on 27.06.17.
 */
public class MainController implements SequentActionListener, RuleApplicationListener {

    private final ProjectManager manager;
    private final BrowserController browserController;
    private final EditorController editorController;
    private final SequentController sequentController;
    private final RuleApplicationController ruleApplicationController;
    private final TimelineLayout view;

    public MainController(ProjectManager manager, ExecutorService executor) {
        this.manager = manager;
        this.browserController = new FlatBrowserController(manager.getProject(), this::onClickPVCEdit);
        //this.browserController = new FileBasedBrowserController(manager.getProject(), this::onClickPVCEdit);
        this.editorController = new EditorController(executor);
        this.sequentController = new SequentController(this);
        this.ruleApplicationController = new RuleApplicationController(this);

        this.view = new TimelineLayout(
                browserController.getView(),
                editorController.getView(),
                sequentController.getView(),
                ruleApplicationController.getRuleApplicationView());
        view.setDividerPosition(0.2);

        browserController.setSelectionListener(this::onSelectBrowserItem);
    }

    public void onClickPVCEdit(PVCEntity entity) {
        PVC pvc = entity.getPVC();
        editorController.viewFile(entity.getLocation());
        editorController.viewPVCSelection(pvc);
        sequentController.viewSequentForPVC(entity, manager.getProofForPVC(entity.getPVC().getIdentifier()));
        ruleApplicationController.resetConsideration();
        view.moveFrameRight();
    }

    public void onSelectBrowserItem(TreeTableEntity treeTableEntity) {
        DafnyFile file = treeTableEntity.getLocation();
        if (file != null) {
            editorController.viewFile(file);
            PVC pvc = treeTableEntity.accept(new PVCGetterVisitor());
            if (pvc != null) {
                editorController.viewPVCSelection(pvc);
            } else {
                editorController.resetPVCSelection();
            }
        }
    }

    @Override
    public void onClickSequentSubterm(TermSelector selector) {
        view.moveFrameRight();
        ProofNode node = sequentController.getActiveProofNode();
        if (node != null) {
            ruleApplicationController.considerApplication(node, node.getSequent(), selector);
        }
    }

    @Override
    public void onRequestReferenceHighlighting(ProofTermReference termRef) {
        if (termRef != null) {
            Set<Reference> predecessors = sequentController.getReferenceGraph().allPredecessors(termRef);
            Set<CodeReference> codeReferences = filterCodeReferences(predecessors);
            editorController.viewReferences(codeReferences);
        } else {
            editorController.viewReferences(new HashSet<>());
        }
    }

    private static Set<CodeReference> filterCodeReferences(Set<Reference> predecessors) {
        Set<CodeReference> codeReferences = new HashSet<>();
        predecessors.forEach(reference -> {
            CodeReference codeReference = reference.accept(new GetReferenceTypeVisitor<>(CodeReference.class));
            if (codeReference != null) {
                codeReferences.add(codeReference);
            }
        });
        return codeReferences;
    }

    @Override
    public void appliedRule(ProofRuleApplication application) {
        ruleApplicationController.applyRule(application);
        String newScript = ruleApplicationController.getScriptView().getText();
        sequentController.getActiveProof().parseAndSetScript(newScript);
        sequentController.tryMovingOn();
        ruleApplicationController.resetConsideration();
    }

    public TimelineLayout getView() {
        return view;
    }
}
