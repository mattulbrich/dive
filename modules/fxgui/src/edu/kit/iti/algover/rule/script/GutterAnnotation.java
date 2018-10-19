package edu.kit.iti.algover.rule.script;

import javafx.beans.binding.BooleanBinding;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * Properties for the annotations for the scriptview gutter
 * @author A. Weigl (PSDBG)
 */
public class GutterAnnotation {
        private StringProperty text = new SimpleStringProperty();

        private SimpleBooleanProperty breakpoint = new SimpleBooleanProperty();

        private StringProperty breakpointCondition = new SimpleStringProperty();

        private BooleanBinding conditional = breakpointCondition.isNotNull().and(breakpointCondition.isNotEmpty());

        private BooleanProperty mainScript = new SimpleBooleanProperty();

        private SimpleBooleanProperty savepoint = new SimpleBooleanProperty();

        //for now specifically for skipped saved commands
        private SimpleBooleanProperty alert = new SimpleBooleanProperty();

        public boolean isAlert() {
            return alert.get();
        }

        public void setAlert(boolean alert) {
            this.alert.set(alert);
        }

        public SimpleBooleanProperty alertProperty() {
            return alert;
        }

        public String getText() {
            return text.get();
        }

        public void setText(String text) {
            this.text.set(text);
        }

        public StringProperty textProperty() {
            return text;
        }

        public boolean isBreakpoint() {
            return breakpoint.get();
        }

        public void setBreakpoint(boolean breakpoint) {
            this.breakpoint.set(breakpoint);
        }

        public SimpleBooleanProperty breakpointProperty() {
            return breakpoint;
        }

        public String getBreakpointCondition() {
            return breakpointCondition.get();
        }

        public void setBreakpointCondition(String breakpointCondition) {
            this.breakpointCondition.set(breakpointCondition);
        }

        public StringProperty breakpointConditionProperty() {
            return breakpointCondition;
        }

        public Boolean getConditional() {
            return conditional.get();
        }

        public BooleanBinding conditionalProperty() {
            return conditional;
        }

        public boolean isMainScript() {
            return mainScript.get();
        }

        public void setMainScript(boolean mainScript) {
            this.mainScript.set(mainScript);
        }

        public BooleanProperty mainScriptProperty() {
            return mainScript;
        }


        public boolean isSavepoint() {
            return savepoint.get();
        }

        public void setSavepoint(boolean savepoint) {
            this.savepoint.set(savepoint);
        }

        public SimpleBooleanProperty savepointProperty() {
            return savepoint;
        }


}
