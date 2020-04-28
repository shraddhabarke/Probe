// Generated from SyGuS.g4 by ANTLR 4.7.2
package sygus;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SyGuSParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.7.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, T__18=19, T__19=20, T__20=21, T__21=22, T__22=23, T__23=24, 
		T__24=25, T__25=26, T__26=27, T__27=28, T__28=29, T__29=30, T__30=31, 
		LineComment=32, WS=33, Numeral=34, Decimal=35, BoolConst=36, HexConst=37, 
		BinConst=38, StringConst=39, Symbol=40;
	public static final int
		RULE_syGuS = 0, RULE_sort = 1, RULE_bfTerm = 2, RULE_term = 3, RULE_sortedVar = 4, 
		RULE_varBinding = 5, RULE_feature = 6, RULE_cmd = 7, RULE_smtCmd = 8, 
		RULE_sortDecl = 9, RULE_dTDec = 10, RULE_dtConsDec = 11, RULE_grammarDef = 12, 
		RULE_groupedRuleList = 13, RULE_gTerm = 14, RULE_identifier = 15, RULE_index = 16, 
		RULE_literal = 17;
	private static String[] makeRuleNames() {
		return new String[] {
			"syGuS", "sort", "bfTerm", "term", "sortedVar", "varBinding", "feature", 
			"cmd", "smtCmd", "sortDecl", "dTDec", "dtConsDec", "grammarDef", "groupedRuleList", 
			"gTerm", "identifier", "index", "literal"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'Int'", "'Bool'", "'Real'", "'('", "'BitVec'", "')'", "'exists'", 
			"'forall'", "'let'", "'grammars'", "'fwd-decls'", "'recursion'", "'check-synth'", 
			"'constraint'", "'declare-var'", "'inv-constraint'", "'set-feature'", 
			"':'", "'synth-fun'", "'synth-inv'", "'declare-datatype'", "'declare-datatypes'", 
			"'declare-sort'", "'define-fun'", "'define-sort'", "'set-info'", "'set-logic'", 
			"'set-option'", "'Constant'", "'Variable'", "'_'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, "LineComment", "WS", 
			"Numeral", "Decimal", "BoolConst", "HexConst", "BinConst", "StringConst", 
			"Symbol"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "SyGuS.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public SyGuSParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class SyGuSContext extends ParserRuleContext {
		public List<CmdContext> cmd() {
			return getRuleContexts(CmdContext.class);
		}
		public CmdContext cmd(int i) {
			return getRuleContext(CmdContext.class,i);
		}
		public SyGuSContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_syGuS; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterSyGuS(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitSyGuS(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitSyGuS(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SyGuSContext syGuS() throws RecognitionException {
		SyGuSContext _localctx = new SyGuSContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_syGuS);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(39);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__3) {
				{
				{
				setState(36);
				cmd();
				}
				}
				setState(41);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SortContext extends ParserRuleContext {
		public IndexContext index() {
			return getRuleContext(IndexContext.class,0);
		}
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public SortContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_sort; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterSort(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitSort(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitSort(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SortContext sort() throws RecognitionException {
		SortContext _localctx = new SortContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_sort);
		try {
			setState(51);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__0:
				enterOuterAlt(_localctx, 1);
				{
				setState(42);
				match(T__0);
				}
				break;
			case T__1:
				enterOuterAlt(_localctx, 2);
				{
				setState(43);
				match(T__1);
				}
				break;
			case T__2:
				enterOuterAlt(_localctx, 3);
				{
				setState(44);
				match(T__2);
				}
				break;
			case T__3:
				enterOuterAlt(_localctx, 4);
				{
				setState(45);
				match(T__3);
				setState(46);
				match(T__4);
				setState(47);
				index();
				setState(48);
				match(T__5);
				}
				break;
			case Symbol:
				enterOuterAlt(_localctx, 5);
				{
				setState(50);
				match(Symbol);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BfTermContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public LiteralContext literal() {
			return getRuleContext(LiteralContext.class,0);
		}
		public List<BfTermContext> bfTerm() {
			return getRuleContexts(BfTermContext.class);
		}
		public BfTermContext bfTerm(int i) {
			return getRuleContext(BfTermContext.class,i);
		}
		public BfTermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bfTerm; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterBfTerm(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitBfTerm(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitBfTerm(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BfTermContext bfTerm() throws RecognitionException {
		BfTermContext _localctx = new BfTermContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_bfTerm);
		int _la;
		try {
			setState(64);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(53);
				identifier();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(54);
				literal();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(55);
				match(T__3);
				setState(56);
				identifier();
				setState(58); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(57);
					bfTerm();
					}
					}
					setState(60); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << Numeral) | (1L << Decimal) | (1L << BoolConst) | (1L << HexConst) | (1L << BinConst) | (1L << StringConst) | (1L << Symbol))) != 0) );
				setState(62);
				match(T__5);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TermContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public LiteralContext literal() {
			return getRuleContext(LiteralContext.class,0);
		}
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public List<SortedVarContext> sortedVar() {
			return getRuleContexts(SortedVarContext.class);
		}
		public SortedVarContext sortedVar(int i) {
			return getRuleContext(SortedVarContext.class,i);
		}
		public List<VarBindingContext> varBinding() {
			return getRuleContexts(VarBindingContext.class);
		}
		public VarBindingContext varBinding(int i) {
			return getRuleContext(VarBindingContext.class,i);
		}
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterTerm(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitTerm(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitTerm(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_term);
		int _la;
		try {
			int _alt;
			setState(109);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,8,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(66);
				identifier();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(67);
				literal();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(68);
				match(T__3);
				setState(69);
				identifier();
				setState(71); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(70);
					term();
					}
					}
					setState(73); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << Numeral) | (1L << Decimal) | (1L << BoolConst) | (1L << HexConst) | (1L << BinConst) | (1L << StringConst) | (1L << Symbol))) != 0) );
				setState(75);
				match(T__5);
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(77);
				match(T__3);
				setState(78);
				match(T__6);
				setState(80); 
				_errHandler.sync(this);
				_alt = 1;
				do {
					switch (_alt) {
					case 1:
						{
						{
						setState(79);
						sortedVar();
						}
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(82); 
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
				} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
				setState(84);
				term();
				setState(85);
				match(T__5);
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(87);
				match(T__3);
				setState(88);
				match(T__7);
				setState(90); 
				_errHandler.sync(this);
				_alt = 1;
				do {
					switch (_alt) {
					case 1:
						{
						{
						setState(89);
						sortedVar();
						}
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					setState(92); 
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
				} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
				setState(94);
				term();
				setState(95);
				match(T__5);
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(97);
				match(T__3);
				setState(98);
				match(T__8);
				setState(99);
				match(T__3);
				setState(101); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(100);
					varBinding();
					}
					}
					setState(103); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__3 );
				setState(105);
				match(T__5);
				setState(106);
				term();
				setState(107);
				match(T__5);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SortedVarContext extends ParserRuleContext {
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public SortedVarContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_sortedVar; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterSortedVar(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitSortedVar(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitSortedVar(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SortedVarContext sortedVar() throws RecognitionException {
		SortedVarContext _localctx = new SortedVarContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_sortedVar);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(111);
			match(T__3);
			setState(112);
			match(Symbol);
			setState(113);
			sort();
			setState(114);
			match(T__5);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarBindingContext extends ParserRuleContext {
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public VarBindingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varBinding; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterVarBinding(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitVarBinding(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitVarBinding(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarBindingContext varBinding() throws RecognitionException {
		VarBindingContext _localctx = new VarBindingContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_varBinding);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(116);
			match(T__3);
			setState(117);
			match(Symbol);
			setState(118);
			term();
			setState(119);
			match(T__5);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FeatureContext extends ParserRuleContext {
		public FeatureContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_feature; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterFeature(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitFeature(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitFeature(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FeatureContext feature() throws RecognitionException {
		FeatureContext _localctx = new FeatureContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_feature);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(121);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__9) | (1L << T__10) | (1L << T__11))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CmdContext extends ParserRuleContext {
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public List<TerminalNode> Symbol() { return getTokens(SyGuSParser.Symbol); }
		public TerminalNode Symbol(int i) {
			return getToken(SyGuSParser.Symbol, i);
		}
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public FeatureContext feature() {
			return getRuleContext(FeatureContext.class,0);
		}
		public TerminalNode BoolConst() { return getToken(SyGuSParser.BoolConst, 0); }
		public List<SortedVarContext> sortedVar() {
			return getRuleContexts(SortedVarContext.class);
		}
		public SortedVarContext sortedVar(int i) {
			return getRuleContext(SortedVarContext.class,i);
		}
		public GrammarDefContext grammarDef() {
			return getRuleContext(GrammarDefContext.class,0);
		}
		public SmtCmdContext smtCmd() {
			return getRuleContext(SmtCmdContext.class,0);
		}
		public CmdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_cmd; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterCmd(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitCmd(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitCmd(this);
			else return visitor.visitChildren(this);
		}
	}

	public final CmdContext cmd() throws RecognitionException {
		CmdContext _localctx = new CmdContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_cmd);
		int _la;
		try {
			setState(184);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,13,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(123);
				match(T__3);
				setState(124);
				match(T__12);
				setState(125);
				match(T__5);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(126);
				match(T__3);
				setState(127);
				match(T__13);
				setState(128);
				term();
				setState(129);
				match(T__5);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(131);
				match(T__3);
				setState(132);
				match(T__14);
				setState(133);
				match(Symbol);
				setState(134);
				sort();
				setState(135);
				match(T__5);
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(137);
				match(T__3);
				setState(138);
				match(T__15);
				setState(139);
				match(Symbol);
				setState(140);
				match(Symbol);
				setState(141);
				match(Symbol);
				setState(142);
				match(Symbol);
				setState(143);
				match(T__5);
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(144);
				match(T__3);
				setState(145);
				match(T__16);
				setState(146);
				match(T__17);
				setState(147);
				feature();
				setState(148);
				match(BoolConst);
				setState(149);
				match(T__5);
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(151);
				match(T__3);
				setState(152);
				match(T__18);
				setState(153);
				match(Symbol);
				setState(154);
				match(T__3);
				setState(158);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(155);
					sortedVar();
					}
					}
					setState(160);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(161);
				match(T__5);
				setState(162);
				sort();
				setState(164);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__3) {
					{
					setState(163);
					grammarDef();
					}
				}

				setState(166);
				match(T__5);
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(168);
				match(T__3);
				setState(169);
				match(T__19);
				setState(170);
				match(Symbol);
				setState(171);
				match(T__3);
				setState(175);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(172);
					sortedVar();
					}
					}
					setState(177);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(178);
				match(T__5);
				setState(180);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__3) {
					{
					setState(179);
					grammarDef();
					}
				}

				setState(182);
				match(T__5);
				}
				break;
			case 8:
				enterOuterAlt(_localctx, 8);
				{
				setState(183);
				smtCmd();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SmtCmdContext extends ParserRuleContext {
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public List<DTDecContext> dTDec() {
			return getRuleContexts(DTDecContext.class);
		}
		public DTDecContext dTDec(int i) {
			return getRuleContext(DTDecContext.class,i);
		}
		public SortDeclContext sortDecl() {
			return getRuleContext(SortDeclContext.class,0);
		}
		public TerminalNode Numeral() { return getToken(SyGuSParser.Numeral, 0); }
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public TermContext term() {
			return getRuleContext(TermContext.class,0);
		}
		public List<SortedVarContext> sortedVar() {
			return getRuleContexts(SortedVarContext.class);
		}
		public SortedVarContext sortedVar(int i) {
			return getRuleContext(SortedVarContext.class,i);
		}
		public LiteralContext literal() {
			return getRuleContext(LiteralContext.class,0);
		}
		public SmtCmdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_smtCmd; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterSmtCmd(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitSmtCmd(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitSmtCmd(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SmtCmdContext smtCmd() throws RecognitionException {
		SmtCmdContext _localctx = new SmtCmdContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_smtCmd);
		int _la;
		try {
			setState(250);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,16,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(186);
				match(T__3);
				setState(187);
				match(T__20);
				setState(188);
				match(Symbol);
				setState(189);
				dTDec();
				setState(190);
				match(T__5);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(192);
				match(T__3);
				setState(193);
				match(T__21);
				setState(194);
				match(T__3);
				setState(195);
				sortDecl();
				setState(196);
				match(T__5);
				setState(197);
				match(T__3);
				setState(199); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(198);
					dTDec();
					}
					}
					setState(201); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__3 );
				setState(203);
				match(T__5);
				setState(204);
				match(T__5);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(206);
				match(T__3);
				setState(207);
				match(T__22);
				setState(208);
				match(Symbol);
				setState(209);
				match(Numeral);
				setState(210);
				match(T__5);
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(211);
				match(T__3);
				setState(212);
				match(T__23);
				setState(213);
				match(Symbol);
				setState(214);
				match(T__3);
				setState(218);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(215);
					sortedVar();
					}
					}
					setState(220);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(221);
				match(T__5);
				setState(222);
				sort();
				setState(223);
				term();
				setState(224);
				match(T__5);
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(226);
				match(T__3);
				setState(227);
				match(T__24);
				setState(228);
				match(Symbol);
				setState(229);
				sort();
				setState(230);
				match(T__5);
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(232);
				match(T__3);
				setState(233);
				match(T__25);
				setState(234);
				match(T__17);
				setState(235);
				match(Symbol);
				setState(236);
				literal();
				setState(237);
				match(T__5);
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(239);
				match(T__3);
				setState(240);
				match(T__26);
				setState(241);
				match(Symbol);
				setState(242);
				match(T__5);
				}
				break;
			case 8:
				enterOuterAlt(_localctx, 8);
				{
				setState(243);
				match(T__3);
				setState(244);
				match(T__27);
				setState(245);
				match(T__17);
				setState(246);
				match(Symbol);
				setState(247);
				literal();
				setState(248);
				match(T__5);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SortDeclContext extends ParserRuleContext {
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public TerminalNode Numeral() { return getToken(SyGuSParser.Numeral, 0); }
		public SortDeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_sortDecl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterSortDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitSortDecl(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitSortDecl(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SortDeclContext sortDecl() throws RecognitionException {
		SortDeclContext _localctx = new SortDeclContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_sortDecl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(252);
			match(T__3);
			setState(253);
			match(Symbol);
			setState(254);
			match(Numeral);
			setState(255);
			match(T__5);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DTDecContext extends ParserRuleContext {
		public List<DtConsDecContext> dtConsDec() {
			return getRuleContexts(DtConsDecContext.class);
		}
		public DtConsDecContext dtConsDec(int i) {
			return getRuleContext(DtConsDecContext.class,i);
		}
		public DTDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_dTDec; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterDTDec(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitDTDec(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitDTDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DTDecContext dTDec() throws RecognitionException {
		DTDecContext _localctx = new DTDecContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_dTDec);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(257);
			match(T__3);
			setState(259); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(258);
				dtConsDec();
				}
				}
				setState(261); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==T__3 );
			setState(263);
			match(T__5);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DtConsDecContext extends ParserRuleContext {
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public List<SortedVarContext> sortedVar() {
			return getRuleContexts(SortedVarContext.class);
		}
		public SortedVarContext sortedVar(int i) {
			return getRuleContext(SortedVarContext.class,i);
		}
		public DtConsDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_dtConsDec; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterDtConsDec(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitDtConsDec(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitDtConsDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DtConsDecContext dtConsDec() throws RecognitionException {
		DtConsDecContext _localctx = new DtConsDecContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_dtConsDec);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(265);
			match(T__3);
			setState(266);
			match(Symbol);
			setState(270);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__3) {
				{
				{
				setState(267);
				sortedVar();
				}
				}
				setState(272);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(273);
			match(T__5);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class GrammarDefContext extends ParserRuleContext {
		public List<GroupedRuleListContext> groupedRuleList() {
			return getRuleContexts(GroupedRuleListContext.class);
		}
		public GroupedRuleListContext groupedRuleList(int i) {
			return getRuleContext(GroupedRuleListContext.class,i);
		}
		public GrammarDefContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_grammarDef; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterGrammarDef(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitGrammarDef(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitGrammarDef(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GrammarDefContext grammarDef() throws RecognitionException {
		GrammarDefContext _localctx = new GrammarDefContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_grammarDef);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(275);
			match(T__3);
			setState(277); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(276);
				groupedRuleList();
				}
				}
				setState(279); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==T__3 );
			setState(281);
			match(T__5);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class GroupedRuleListContext extends ParserRuleContext {
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public List<GTermContext> gTerm() {
			return getRuleContexts(GTermContext.class);
		}
		public GTermContext gTerm(int i) {
			return getRuleContext(GTermContext.class,i);
		}
		public GroupedRuleListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_groupedRuleList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterGroupedRuleList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitGroupedRuleList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitGroupedRuleList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GroupedRuleListContext groupedRuleList() throws RecognitionException {
		GroupedRuleListContext _localctx = new GroupedRuleListContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_groupedRuleList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(283);
			match(T__3);
			setState(284);
			match(Symbol);
			setState(285);
			sort();
			setState(286);
			match(T__3);
			setState(288); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(287);
				gTerm();
				}
				}
				setState(290); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << Numeral) | (1L << Decimal) | (1L << BoolConst) | (1L << HexConst) | (1L << BinConst) | (1L << StringConst) | (1L << Symbol))) != 0) );
			setState(292);
			match(T__5);
			setState(293);
			match(T__5);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class GTermContext extends ParserRuleContext {
		public SortContext sort() {
			return getRuleContext(SortContext.class,0);
		}
		public BfTermContext bfTerm() {
			return getRuleContext(BfTermContext.class,0);
		}
		public GTermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_gTerm; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterGTerm(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitGTerm(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitGTerm(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GTermContext gTerm() throws RecognitionException {
		GTermContext _localctx = new GTermContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_gTerm);
		try {
			setState(306);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,21,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(295);
				match(T__3);
				setState(296);
				match(T__28);
				setState(297);
				sort();
				setState(298);
				match(T__5);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(300);
				match(T__3);
				setState(301);
				match(T__29);
				setState(302);
				sort();
				setState(303);
				match(T__5);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(305);
				bfTerm();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IdentifierContext extends ParserRuleContext {
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public List<IndexContext> index() {
			return getRuleContexts(IndexContext.class);
		}
		public IndexContext index(int i) {
			return getRuleContext(IndexContext.class,i);
		}
		public IdentifierContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_identifier; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterIdentifier(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitIdentifier(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitIdentifier(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IdentifierContext identifier() throws RecognitionException {
		IdentifierContext _localctx = new IdentifierContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_identifier);
		int _la;
		try {
			setState(319);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case Symbol:
				enterOuterAlt(_localctx, 1);
				{
				setState(308);
				match(Symbol);
				}
				break;
			case T__3:
				enterOuterAlt(_localctx, 2);
				{
				setState(309);
				match(T__3);
				setState(310);
				match(T__30);
				setState(311);
				match(Symbol);
				setState(313); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(312);
					index();
					}
					}
					setState(315); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==Numeral || _la==Symbol );
				setState(317);
				match(T__5);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IndexContext extends ParserRuleContext {
		public TerminalNode Numeral() { return getToken(SyGuSParser.Numeral, 0); }
		public TerminalNode Symbol() { return getToken(SyGuSParser.Symbol, 0); }
		public IndexContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_index; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterIndex(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitIndex(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitIndex(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IndexContext index() throws RecognitionException {
		IndexContext _localctx = new IndexContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_index);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(321);
			_la = _input.LA(1);
			if ( !(_la==Numeral || _la==Symbol) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LiteralContext extends ParserRuleContext {
		public TerminalNode Numeral() { return getToken(SyGuSParser.Numeral, 0); }
		public TerminalNode Decimal() { return getToken(SyGuSParser.Decimal, 0); }
		public TerminalNode BoolConst() { return getToken(SyGuSParser.BoolConst, 0); }
		public TerminalNode HexConst() { return getToken(SyGuSParser.HexConst, 0); }
		public TerminalNode BinConst() { return getToken(SyGuSParser.BinConst, 0); }
		public TerminalNode StringConst() { return getToken(SyGuSParser.StringConst, 0); }
		public LiteralContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_literal; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).enterLiteral(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SyGuSListener ) ((SyGuSListener)listener).exitLiteral(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SyGuSVisitor ) return ((SyGuSVisitor<? extends T>)visitor).visitLiteral(this);
			else return visitor.visitChildren(this);
		}
	}

	public final LiteralContext literal() throws RecognitionException {
		LiteralContext _localctx = new LiteralContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_literal);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(323);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << Numeral) | (1L << Decimal) | (1L << BoolConst) | (1L << HexConst) | (1L << BinConst) | (1L << StringConst))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3*\u0148\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\3\2\7\2(\n\2\f\2\16\2+\13\2\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3"+
		"\3\3\5\3\66\n\3\3\4\3\4\3\4\3\4\3\4\6\4=\n\4\r\4\16\4>\3\4\3\4\5\4C\n"+
		"\4\3\5\3\5\3\5\3\5\3\5\6\5J\n\5\r\5\16\5K\3\5\3\5\3\5\3\5\3\5\6\5S\n\5"+
		"\r\5\16\5T\3\5\3\5\3\5\3\5\3\5\3\5\6\5]\n\5\r\5\16\5^\3\5\3\5\3\5\3\5"+
		"\3\5\3\5\3\5\6\5h\n\5\r\5\16\5i\3\5\3\5\3\5\3\5\5\5p\n\5\3\6\3\6\3\6\3"+
		"\6\3\6\3\7\3\7\3\7\3\7\3\7\3\b\3\b\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t"+
		"\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3"+
		"\t\3\t\3\t\3\t\3\t\3\t\3\t\7\t\u009f\n\t\f\t\16\t\u00a2\13\t\3\t\3\t\3"+
		"\t\5\t\u00a7\n\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\7\t\u00b0\n\t\f\t\16\t\u00b3"+
		"\13\t\3\t\3\t\5\t\u00b7\n\t\3\t\3\t\5\t\u00bb\n\t\3\n\3\n\3\n\3\n\3\n"+
		"\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\6\n\u00ca\n\n\r\n\16\n\u00cb\3\n\3\n"+
		"\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\7\n\u00db\n\n\f\n\16\n\u00de"+
		"\13\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n"+
		"\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\5\n\u00fd\n\n\3\13"+
		"\3\13\3\13\3\13\3\13\3\f\3\f\6\f\u0106\n\f\r\f\16\f\u0107\3\f\3\f\3\r"+
		"\3\r\3\r\7\r\u010f\n\r\f\r\16\r\u0112\13\r\3\r\3\r\3\16\3\16\6\16\u0118"+
		"\n\16\r\16\16\16\u0119\3\16\3\16\3\17\3\17\3\17\3\17\3\17\6\17\u0123\n"+
		"\17\r\17\16\17\u0124\3\17\3\17\3\17\3\20\3\20\3\20\3\20\3\20\3\20\3\20"+
		"\3\20\3\20\3\20\3\20\5\20\u0135\n\20\3\21\3\21\3\21\3\21\3\21\6\21\u013c"+
		"\n\21\r\21\16\21\u013d\3\21\3\21\5\21\u0142\n\21\3\22\3\22\3\23\3\23\3"+
		"\23\2\2\24\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \"$\2\5\3\2\f\16\4\2"+
		"$$**\3\2$)\2\u0162\2)\3\2\2\2\4\65\3\2\2\2\6B\3\2\2\2\bo\3\2\2\2\nq\3"+
		"\2\2\2\fv\3\2\2\2\16{\3\2\2\2\20\u00ba\3\2\2\2\22\u00fc\3\2\2\2\24\u00fe"+
		"\3\2\2\2\26\u0103\3\2\2\2\30\u010b\3\2\2\2\32\u0115\3\2\2\2\34\u011d\3"+
		"\2\2\2\36\u0134\3\2\2\2 \u0141\3\2\2\2\"\u0143\3\2\2\2$\u0145\3\2\2\2"+
		"&(\5\20\t\2\'&\3\2\2\2(+\3\2\2\2)\'\3\2\2\2)*\3\2\2\2*\3\3\2\2\2+)\3\2"+
		"\2\2,\66\7\3\2\2-\66\7\4\2\2.\66\7\5\2\2/\60\7\6\2\2\60\61\7\7\2\2\61"+
		"\62\5\"\22\2\62\63\7\b\2\2\63\66\3\2\2\2\64\66\7*\2\2\65,\3\2\2\2\65-"+
		"\3\2\2\2\65.\3\2\2\2\65/\3\2\2\2\65\64\3\2\2\2\66\5\3\2\2\2\67C\5 \21"+
		"\28C\5$\23\29:\7\6\2\2:<\5 \21\2;=\5\6\4\2<;\3\2\2\2=>\3\2\2\2><\3\2\2"+
		"\2>?\3\2\2\2?@\3\2\2\2@A\7\b\2\2AC\3\2\2\2B\67\3\2\2\2B8\3\2\2\2B9\3\2"+
		"\2\2C\7\3\2\2\2Dp\5 \21\2Ep\5$\23\2FG\7\6\2\2GI\5 \21\2HJ\5\b\5\2IH\3"+
		"\2\2\2JK\3\2\2\2KI\3\2\2\2KL\3\2\2\2LM\3\2\2\2MN\7\b\2\2Np\3\2\2\2OP\7"+
		"\6\2\2PR\7\t\2\2QS\5\n\6\2RQ\3\2\2\2ST\3\2\2\2TR\3\2\2\2TU\3\2\2\2UV\3"+
		"\2\2\2VW\5\b\5\2WX\7\b\2\2Xp\3\2\2\2YZ\7\6\2\2Z\\\7\n\2\2[]\5\n\6\2\\"+
		"[\3\2\2\2]^\3\2\2\2^\\\3\2\2\2^_\3\2\2\2_`\3\2\2\2`a\5\b\5\2ab\7\b\2\2"+
		"bp\3\2\2\2cd\7\6\2\2de\7\13\2\2eg\7\6\2\2fh\5\f\7\2gf\3\2\2\2hi\3\2\2"+
		"\2ig\3\2\2\2ij\3\2\2\2jk\3\2\2\2kl\7\b\2\2lm\5\b\5\2mn\7\b\2\2np\3\2\2"+
		"\2oD\3\2\2\2oE\3\2\2\2oF\3\2\2\2oO\3\2\2\2oY\3\2\2\2oc\3\2\2\2p\t\3\2"+
		"\2\2qr\7\6\2\2rs\7*\2\2st\5\4\3\2tu\7\b\2\2u\13\3\2\2\2vw\7\6\2\2wx\7"+
		"*\2\2xy\5\b\5\2yz\7\b\2\2z\r\3\2\2\2{|\t\2\2\2|\17\3\2\2\2}~\7\6\2\2~"+
		"\177\7\17\2\2\177\u00bb\7\b\2\2\u0080\u0081\7\6\2\2\u0081\u0082\7\20\2"+
		"\2\u0082\u0083\5\b\5\2\u0083\u0084\7\b\2\2\u0084\u00bb\3\2\2\2\u0085\u0086"+
		"\7\6\2\2\u0086\u0087\7\21\2\2\u0087\u0088\7*\2\2\u0088\u0089\5\4\3\2\u0089"+
		"\u008a\7\b\2\2\u008a\u00bb\3\2\2\2\u008b\u008c\7\6\2\2\u008c\u008d\7\22"+
		"\2\2\u008d\u008e\7*\2\2\u008e\u008f\7*\2\2\u008f\u0090\7*\2\2\u0090\u0091"+
		"\7*\2\2\u0091\u00bb\7\b\2\2\u0092\u0093\7\6\2\2\u0093\u0094\7\23\2\2\u0094"+
		"\u0095\7\24\2\2\u0095\u0096\5\16\b\2\u0096\u0097\7&\2\2\u0097\u0098\7"+
		"\b\2\2\u0098\u00bb\3\2\2\2\u0099\u009a\7\6\2\2\u009a\u009b\7\25\2\2\u009b"+
		"\u009c\7*\2\2\u009c\u00a0\7\6\2\2\u009d\u009f\5\n\6\2\u009e\u009d\3\2"+
		"\2\2\u009f\u00a2\3\2\2\2\u00a0\u009e\3\2\2\2\u00a0\u00a1\3\2\2\2\u00a1"+
		"\u00a3\3\2\2\2\u00a2\u00a0\3\2\2\2\u00a3\u00a4\7\b\2\2\u00a4\u00a6\5\4"+
		"\3\2\u00a5\u00a7\5\32\16\2\u00a6\u00a5\3\2\2\2\u00a6\u00a7\3\2\2\2\u00a7"+
		"\u00a8\3\2\2\2\u00a8\u00a9\7\b\2\2\u00a9\u00bb\3\2\2\2\u00aa\u00ab\7\6"+
		"\2\2\u00ab\u00ac\7\26\2\2\u00ac\u00ad\7*\2\2\u00ad\u00b1\7\6\2\2\u00ae"+
		"\u00b0\5\n\6\2\u00af\u00ae\3\2\2\2\u00b0\u00b3\3\2\2\2\u00b1\u00af\3\2"+
		"\2\2\u00b1\u00b2\3\2\2\2\u00b2\u00b4\3\2\2\2\u00b3\u00b1\3\2\2\2\u00b4"+
		"\u00b6\7\b\2\2\u00b5\u00b7\5\32\16\2\u00b6\u00b5\3\2\2\2\u00b6\u00b7\3"+
		"\2\2\2\u00b7\u00b8\3\2\2\2\u00b8\u00bb\7\b\2\2\u00b9\u00bb\5\22\n\2\u00ba"+
		"}\3\2\2\2\u00ba\u0080\3\2\2\2\u00ba\u0085\3\2\2\2\u00ba\u008b\3\2\2\2"+
		"\u00ba\u0092\3\2\2\2\u00ba\u0099\3\2\2\2\u00ba\u00aa\3\2\2\2\u00ba\u00b9"+
		"\3\2\2\2\u00bb\21\3\2\2\2\u00bc\u00bd\7\6\2\2\u00bd\u00be\7\27\2\2\u00be"+
		"\u00bf\7*\2\2\u00bf\u00c0\5\26\f\2\u00c0\u00c1\7\b\2\2\u00c1\u00fd\3\2"+
		"\2\2\u00c2\u00c3\7\6\2\2\u00c3\u00c4\7\30\2\2\u00c4\u00c5\7\6\2\2\u00c5"+
		"\u00c6\5\24\13\2\u00c6\u00c7\7\b\2\2\u00c7\u00c9\7\6\2\2\u00c8\u00ca\5"+
		"\26\f\2\u00c9\u00c8\3\2\2\2\u00ca\u00cb\3\2\2\2\u00cb\u00c9\3\2\2\2\u00cb"+
		"\u00cc\3\2\2\2\u00cc\u00cd\3\2\2\2\u00cd\u00ce\7\b\2\2\u00ce\u00cf\7\b"+
		"\2\2\u00cf\u00fd\3\2\2\2\u00d0\u00d1\7\6\2\2\u00d1\u00d2\7\31\2\2\u00d2"+
		"\u00d3\7*\2\2\u00d3\u00d4\7$\2\2\u00d4\u00fd\7\b\2\2\u00d5\u00d6\7\6\2"+
		"\2\u00d6\u00d7\7\32\2\2\u00d7\u00d8\7*\2\2\u00d8\u00dc\7\6\2\2\u00d9\u00db"+
		"\5\n\6\2\u00da\u00d9\3\2\2\2\u00db\u00de\3\2\2\2\u00dc\u00da\3\2\2\2\u00dc"+
		"\u00dd\3\2\2\2\u00dd\u00df\3\2\2\2\u00de\u00dc\3\2\2\2\u00df\u00e0\7\b"+
		"\2\2\u00e0\u00e1\5\4\3\2\u00e1\u00e2\5\b\5\2\u00e2\u00e3\7\b\2\2\u00e3"+
		"\u00fd\3\2\2\2\u00e4\u00e5\7\6\2\2\u00e5\u00e6\7\33\2\2\u00e6\u00e7\7"+
		"*\2\2\u00e7\u00e8\5\4\3\2\u00e8\u00e9\7\b\2\2\u00e9\u00fd\3\2\2\2\u00ea"+
		"\u00eb\7\6\2\2\u00eb\u00ec\7\34\2\2\u00ec\u00ed\7\24\2\2\u00ed\u00ee\7"+
		"*\2\2\u00ee\u00ef\5$\23\2\u00ef\u00f0\7\b\2\2\u00f0\u00fd\3\2\2\2\u00f1"+
		"\u00f2\7\6\2\2\u00f2\u00f3\7\35\2\2\u00f3\u00f4\7*\2\2\u00f4\u00fd\7\b"+
		"\2\2\u00f5\u00f6\7\6\2\2\u00f6\u00f7\7\36\2\2\u00f7\u00f8\7\24\2\2\u00f8"+
		"\u00f9\7*\2\2\u00f9\u00fa\5$\23\2\u00fa\u00fb\7\b\2\2\u00fb\u00fd\3\2"+
		"\2\2\u00fc\u00bc\3\2\2\2\u00fc\u00c2\3\2\2\2\u00fc\u00d0\3\2\2\2\u00fc"+
		"\u00d5\3\2\2\2\u00fc\u00e4\3\2\2\2\u00fc\u00ea\3\2\2\2\u00fc\u00f1\3\2"+
		"\2\2\u00fc\u00f5\3\2\2\2\u00fd\23\3\2\2\2\u00fe\u00ff\7\6\2\2\u00ff\u0100"+
		"\7*\2\2\u0100\u0101\7$\2\2\u0101\u0102\7\b\2\2\u0102\25\3\2\2\2\u0103"+
		"\u0105\7\6\2\2\u0104\u0106\5\30\r\2\u0105\u0104\3\2\2\2\u0106\u0107\3"+
		"\2\2\2\u0107\u0105\3\2\2\2\u0107\u0108\3\2\2\2\u0108\u0109\3\2\2\2\u0109"+
		"\u010a\7\b\2\2\u010a\27\3\2\2\2\u010b\u010c\7\6\2\2\u010c\u0110\7*\2\2"+
		"\u010d\u010f\5\n\6\2\u010e\u010d\3\2\2\2\u010f\u0112\3\2\2\2\u0110\u010e"+
		"\3\2\2\2\u0110\u0111\3\2\2\2\u0111\u0113\3\2\2\2\u0112\u0110\3\2\2\2\u0113"+
		"\u0114\7\b\2\2\u0114\31\3\2\2\2\u0115\u0117\7\6\2\2\u0116\u0118\5\34\17"+
		"\2\u0117\u0116\3\2\2\2\u0118\u0119\3\2\2\2\u0119\u0117\3\2\2\2\u0119\u011a"+
		"\3\2\2\2\u011a\u011b\3\2\2\2\u011b\u011c\7\b\2\2\u011c\33\3\2\2\2\u011d"+
		"\u011e\7\6\2\2\u011e\u011f\7*\2\2\u011f\u0120\5\4\3\2\u0120\u0122\7\6"+
		"\2\2\u0121\u0123\5\36\20\2\u0122\u0121\3\2\2\2\u0123\u0124\3\2\2\2\u0124"+
		"\u0122\3\2\2\2\u0124\u0125\3\2\2\2\u0125\u0126\3\2\2\2\u0126\u0127\7\b"+
		"\2\2\u0127\u0128\7\b\2\2\u0128\35\3\2\2\2\u0129\u012a\7\6\2\2\u012a\u012b"+
		"\7\37\2\2\u012b\u012c\5\4\3\2\u012c\u012d\7\b\2\2\u012d\u0135\3\2\2\2"+
		"\u012e\u012f\7\6\2\2\u012f\u0130\7 \2\2\u0130\u0131\5\4\3\2\u0131\u0132"+
		"\7\b\2\2\u0132\u0135\3\2\2\2\u0133\u0135\5\6\4\2\u0134\u0129\3\2\2\2\u0134"+
		"\u012e\3\2\2\2\u0134\u0133\3\2\2\2\u0135\37\3\2\2\2\u0136\u0142\7*\2\2"+
		"\u0137\u0138\7\6\2\2\u0138\u0139\7!\2\2\u0139\u013b\7*\2\2\u013a\u013c"+
		"\5\"\22\2\u013b\u013a\3\2\2\2\u013c\u013d\3\2\2\2\u013d\u013b\3\2\2\2"+
		"\u013d\u013e\3\2\2\2\u013e\u013f\3\2\2\2\u013f\u0140\7\b\2\2\u0140\u0142"+
		"\3\2\2\2\u0141\u0136\3\2\2\2\u0141\u0137\3\2\2\2\u0142!\3\2\2\2\u0143"+
		"\u0144\t\3\2\2\u0144#\3\2\2\2\u0145\u0146\t\4\2\2\u0146%\3\2\2\2\32)\65"+
		">BKT^io\u00a0\u00a6\u00b1\u00b6\u00ba\u00cb\u00dc\u00fc\u0107\u0110\u0119"+
		"\u0124\u0134\u013d\u0141";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}