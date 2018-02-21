package edu.kit.iti.algover;

import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.browser.entities.PVCGetterVisitor;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.*;
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

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ExecutorService;

/**
 * Created by philipp on 27.06.17.
 */
public class MainController implements SequentActionListener, RuleApplicationListener {

    private final ProjectManager manager;
    private final TimelineLayout view;

    // All controllers for the views, sorted from left-to-right in the way they appear in the GUI
    private final BrowserController browserController;
    private final EditorController editorController;
    private final SequentController sequentController;
    private final RuleApplicationController ruleApplicationController;

    public MainController(ProjectManager manager, ExecutorService executor) {
        this.manager = manager;
        this.browserController = new FlatBrowserController(manager.getProject(), manager.getAllProofs(), this::onClickPVCEdit);
        //this.browserController = new FileBasedBrowserController(manager.getProject(), manager.getAllProofs(), this::onClickPVCEdit);
        this.editorController = new EditorController(executor);
        this.sequentController = new SequentController(this);
        this.ruleApplicationController = new RuleApplicationController(executor, this);

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
        Proof proof = manager.getProofForPVC(entity.getPVC().getIdentifier());
        // MU: currently proofs are not automatically interpreted and/or uptodate. Make sure they are.
        if(proof.getProofStatus() == ProofStatus.NON_EXISTING  || proof.getProofStatus() == ProofStatus.CHANGED_SCRIPT)
            proof.interpretScript();
        sequentController.viewSequentForPVC(entity, proof);
        ruleApplicationController.resetConsideration();
        ruleApplicationController.getScriptController().setProof(proof);
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
        ProofNode node = sequentController.getActiveNode();
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
    public void onPreviewRuleApplication(ProofRuleApplication application) {
        sequentController.viewProofApplicationPreview(application);
    }

    @Override
    public void onResetRuleApplicationPreview() {
        sequentController.resetProofApplicationPreview();
    }

    @Override
    public void onRuleApplication(ProofRuleApplication application) {
        // This can be implemented as an incremental algorithm in the future here!
        // Currently, this will reset the script text completely. That means the
        // script has to be parsed and rebuilt completely.
        ruleApplicationController.applyRule(application);
        ruleApplicationController.getRuleGrid().getSelectionModel().clearSelection();
        String newScript = ruleApplicationController.getScriptView().getText();
        sequentController.getActiveProof().setScriptTextAndInterpret(newScript);
        sequentController.tryMovingOn();
        ruleApplicationController.resetConsideration();
    }

    @Override
    public void onScriptSave() {
        String pvcIdentifier = sequentController.getActiveProof().getPVC().getIdentifier();
        try {
            manager.saveProofScriptForPVC(pvcIdentifier, sequentController.getActiveProof());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * when the user clicked somewhere in the proof script to change the proof node that should be viewed
     */
    @Override
    public void onSwitchViewedNode(ProofNodeSelector proofNodeSelector) {
        sequentController.viewProofNode(proofNodeSelector);
    }

    public TimelineLayout getView() {
        return view;
    }
}
