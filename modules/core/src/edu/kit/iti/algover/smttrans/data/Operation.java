package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;

import java.util.List;


public enum Operation {

	PLUS, MINUS, TIMES, GT, LT, EQ, NOT, GE, LE, NEG, ITE, ARR2SELECT, ARRSTORE, ARR2STORE, FIELDSTORE, FIELDSELECT, DECR, SETUNION, SETINTERSECT, SETCARD, SEQCONCAT, ISCREATED, CREATE, ANON, SEQCONS, SEQEMPTY, SEQUPD, SEQGET, SEQLEN, SETIN, SETADD, CONST, ARRLEN, ARR2LEN0, ARR2LEN1, EXISTS, FORALL, LET, ARRSELECT;

	private String smt;
	private Boolean poly;
//	private DeclType type;
	private List<Axiom> instantiations = new ArrayList<>();

	static {
	    
	    ARRSELECT.smt = "arrselect";
	    ARRSELECT.poly = true;
//	    ARR2SELECT.type = DeclType.ARR;
		ARR2LEN0.smt = "arr2len0";
		ARR2LEN0.poly = true;
	//	ARR2LEN0.type = DeclType.ARR2;
		

		ARR2LEN1.smt = "arr2len1";
		ARR2LEN1.poly = true;
		//ARR2LEN1.type = DeclType.ARR2;

		ARRLEN.smt = "arrlen";
		ARRLEN.poly = true;
		//ARRLEN.type = DeclType.ARR;

		PLUS.smt = "+";
		PLUS.poly = false;
	//	PLUS.type = DeclType.NONE;

		MINUS.smt = "-";
		MINUS.poly = false;
		//MINUS.type = DeclType.NONE;

		TIMES.smt = "*";
		TIMES.poly = false;
		//TIMES.type = DeclType.NONE;

		GT.smt = ">";
		GT.poly = false;
		//GT.type = DeclType.NONE;

		LT.smt = "<";
		LT.poly = false;
		//LT.type = DeclType.NONE;

		EQ.smt = "=";
		EQ.poly = false;
		//EQ.type = DeclType.ANY;

		NOT.smt = "not";
		NOT.poly = false;
		//NOT.type = DeclType.NONE;

		GE.smt = ">=";
		GE.poly = false;
		//GE.type = DeclType.NONE;

		LE.smt = "<=";
		LE.poly = false;
		//LE.type = DeclType.NONE;

		NEG.smt = "";
		NEG.poly = false;
		//NEG.type = DeclType.NONE;

		ITE.smt = "";
		ITE.poly = false;

		ARR2SELECT.smt = "";
		ARR2SELECT.poly = true;
		//ARR2SELECT.type = DeclType.ARR2;

		ARRSTORE.smt = "";
		ARRSTORE.poly = true;
		//ARRSTORE.type = DeclType.ARR;

		ARR2STORE.smt = "";
		ARR2STORE.poly = true;
		//ARR2STORE.type = DeclType.ARR2;

		FIELDSTORE.smt = "";
		FIELDSTORE.poly = true;
		//FIELDSTORE.type = DeclType.SORT;

		FIELDSELECT.smt = "";
		FIELDSELECT.poly = true;
		//FIELDSTORE.type = DeclType.SORT;

		DECR.smt = "";
		DECR.poly = false;

		SETUNION.smt = "";
		SETUNION.poly = true;
		//SETUNION.type = DeclType.SET;

		SETINTERSECT.smt = "";
		SETINTERSECT.poly = true;
		//SETINTERSECT.type = DeclType.SET;

		SETCARD.smt = "";
		SETCARD.poly = true;
		//SETCARD.type = DeclType.SET;

		SEQCONCAT.smt = "";
		SEQCONCAT.poly = true;
		//SEQCONCAT.type = DeclType.SEQ;

		ISCREATED.smt = "";
		ISCREATED.poly = true;
	//	ISCREATED.type = DeclType.SORT;

		CREATE.smt = "";
		CREATE.poly = true;
//		CREATE.type = DeclType.SORT;

		ANON.smt = "";
		ANON.poly = false;
		//ANON.type = DeclType.SORT;

		SEQCONS.smt = "";
		SEQCONS.poly = true;
		//SEQCONS.type = DeclType.SEQ;

		SEQEMPTY.smt = "";
		SEQEMPTY.poly = true;
		//SEQEMPTY.type = DeclType.SEQ;

		SEQUPD.smt = "";
		SEQUPD.poly = true;
		//SEQUPD.type = DeclType.SEQ;

		SEQGET.smt = "";
		SEQGET.poly = true;
		//SEQGET.type = DeclType.SEQ;

		SEQLEN.smt = "";
		SEQLEN.poly = true;
	//	SEQLEN.type = DeclType.SEQ;

		SETIN.smt = "";
		SETIN.poly = true;
//		SETIN.type = DeclType.SET;

		SETADD.smt = "";
		SETADD.poly = true;
		//SETADD.type = DeclType.SET;
	}

	public String toSMTLib(List<String> type) {
		// special cases here ...

		if (poly) {
			String typedSMT = smt;
			for (String t : type) {
				typedSMT += t;
			}
			return typedSMT;
		}
		return smt;
	}
	

	
	public Boolean getPoly() {
		return poly;
	}


}
