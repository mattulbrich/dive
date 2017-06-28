package edu.kit.iti.algover.settings;

import java.util.HashMap;

/**
 * ProjectSettings:
 * * symbex settings: unwind loop, inline methods, use contract
 * * ProverSettings: timeout for z3/dafny/key (DONE), save intermediate po files
 * * ViewSettings: logical view: display ssa; automatically apply simplification, fontsize, tooltipsize
 * * smt settings for cex
 * Created by sarah on 8/3/16.
 * has to be called by projectbuilder
 */
public class ProjectSettings{

    /**
     *Settings atm available
     */
    public static final String DAFNY_TIMEOUT = "Dafny Timeout";
    public static final String KEY_TIMEOUT = "KeY Timeout";
    public static final String SMT_TIMEOUT = "SMT Timeout";

    public static final String SYMBEX_UNROLL_LOOPS = "Unroll Loops";
    public static final String SYMBEX_INLINE_METHODS = "Unroll Loops";


    /**
     * data structure holding values of the settings
     */
    public HashMap<String, String> set;
    public ProjectSettings(){
        set= new HashMap<>();
        setDefaultValues();
    }


    public String getValue(String key){
        if(this.set.containsKey(key)){
           return this.set.get(key);
        }
        return null;
    }

    /**
     * Set default values for all settings
     */
    public void setDefaultValues(){
        set.put(DAFNY_TIMEOUT, "5");
        set.put(KEY_TIMEOUT, "10");
        set.put(SMT_TIMEOUT, "10");
        set.put(SYMBEX_INLINE_METHODS, "false");
        set.put(SYMBEX_UNROLL_LOOPS, "false");
    }

    /**
     * Set settings
     * @param setting
     * @param value
     */
    public void setValue(String setting, String value){
        if (set.containsKey(setting)){
            set.remove(setting);
            set.put(setting, value);
        }else{
            set.put(setting, value);

        }
    }

    public String toString(){
        String ret ="Settings: \n";
        for (String s : set.keySet()) {
            ret += s+": "+set.get(s)+"\n";
        }
        return ret;
    }


    public HashMap getSettings(){
        return this.set;
    }
}



