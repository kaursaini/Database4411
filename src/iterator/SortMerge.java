package iterator;

import heap.*;
import global.*;
import diskmgr.*;
import bufmgr.*;
import index.*;
import java.io.*;

/*==========================================================================*/
/**
 * Sort-merge join. Call the two relations being joined R (outer) and S (inner).
 * This is an implementation of the naive sort-merge join algorithm. The
 * external sorting utility is used to generate runs. Then the iterator
 * interface is called to fetch successive tuples for the final merge with
 * joining.
 */

public class SortMerge extends Iterator implements GlobalConst {

	// constructor parameters
	private AttrType in1[];
	private AttrType in2[];

	private int join_col_in1;
	private int join_col_in2;

	private Iterator am1;
	private Iterator am2;

	private TupleOrder order;

	private CondExpr outFilter[];
	private FldSpec proj_list[];
	private int n_out_flds;

	// other variables
	private boolean firstScan;
	private boolean scanDone;
	private boolean goodTuple;

	private Tuple tupleR;
	private Tuple tupleS;
	private Tuple tupleRCopy; // tuple to keep copy of tupleR
	private Tuple tupleSCopy; // tuple to keep copy of tupleS

	// ioBuf and related variables
	private IoBuf ioBufR = new IoBuf(); // ioBuf to store tuples for R
	private IoBuf ioBufS = new IoBuf(); // ioBuf to store tuples for S
	private byte matchSpaceR[][];
	private byte matchSpaceS[][];
	private Heapfile innerHeapR;
	private Heapfile innerHeapS;

	// joinTuple to return the merged tuple from R and S
	private Tuple joinTuple;
	AttrType[] joinTypes;
	short[] ts_size = null;

	/**
	 * constructor,initialization
	 * 
	 * @param              in1[] Array containing field types of R
	 * @param len_in1      # of columns in R
	 * @param s1_sizes     Shows the length of the string fields in R.
	 * @param              in2[] Array containing field types of S
	 * @param len_in2      # of columns in S
	 * @param s2_sizes     Shows the length of the string fields in S
	 * @param sortFld1Len  The length of sorted field in R
	 * @param sortFld2Len  The length of sorted field in S
	 * @param join_col_in1 The column of R to be joined with S
	 * @param join_col_in2 The column of S to be joined with R
	 * @param amt_of_mem   Amount of memory available, in pages
	 * @param am1          Access method for left input to join
	 * @param am2          Access method for right input to join
	 * @param in1_sorted   Is am1 sorted?
	 * @param in2_sorted   Is am2 sorted?
	 * @param order        The order of the tuple: ascending or descending?
	 * @param              outFilter[] Pointer to the output filter
	 * @param proj_list    Shows what input fields go where in the output tuple
	 * @param n_out_flds   Number of outer relation fields
	 * @exception JoinNewFailed             Allocate failed
	 * @exception JoinLowMemory             Memory not enough
	 * @exception SortException             Exception from sorting
	 * @exception TupleUtilsException       Exception from using tuple utils
	 * @exception JoinsException            Exception reading stream
	 * @exception IndexException            Exception...
	 * @exception InvalidTupleSizeException Exception...
	 * @exception InvalidTypeException      Exception...
	 * @exception PageNotReadException      Exception...
	 * @exception PredEvalException         Exception...
	 * @exception LowMemException           Exception...
	 * @exception UnknowAttrType            Exception...
	 * @exception UnknownKeyTypeException   Exception...
	 * @exception IOException               Some I/O fault
	 * @exception Exception                 Generic
	 */

	public SortMerge(AttrType in1[], int len_in1, short s1_sizes[], AttrType in2[], int len_in2, short s2_sizes[],

			int join_col_in1, int sortFld1Len, int join_col_in2, int sortFld2Len,

			int amt_of_mem, Iterator am1, Iterator am2,

			boolean in1_sorted, boolean in2_sorted, TupleOrder order,

			CondExpr outFilter[], FldSpec proj_list[], int n_out_flds)
			throws JoinNewFailed, JoinLowMemory, SortException, TupleUtilsException, JoinsException, IndexException,
			InvalidTupleSizeException, InvalidTypeException, PageNotReadException, PredEvalException, LowMemException,
			UnknowAttrType, UnknownKeyTypeException, IOException, Exception {

		// this.in1 = in1;
		// this.in2 = in2;
		this.in1 = new AttrType[in1.length];
		this.in2 = new AttrType[in2.length];

		this.join_col_in1 = join_col_in1;
		this.join_col_in2 = join_col_in2;

		this.order = order;

		this.outFilter = outFilter;
		this.proj_list = proj_list;
		this.n_out_flds = n_out_flds;

		System.arraycopy(in1, 0, this.in1, 0, in1.length);
		System.arraycopy(in2, 0, this.in2, 0, in2.length);
		
		// Initializing original tuples and their copies to be made
		tupleR = new Tuple();
		tupleS = new Tuple();
		tupleRCopy = new Tuple();
		tupleSCopy = new Tuple();

		// checking amt_of_mem

		if (amt_of_mem < 2) {
			throw new JoinLowMemory("Sort-Merge Constructor: amount of memory less than 2");
		}
		else if (ioBufR == null || ioBufS == null) {
			throw new JoinNewFailed("Sort-Merge Constructor: allocate failed");
		}
		else if (tupleR == null || tupleS == null || tupleRCopy == null || tupleSCopy == null) {
			throw new JoinLowMemory("Sort-Merge Constructor: tuple allocation failed");
			
		}
		else {

			/*
			 * checking if relations R and S are sorted if not, call the sort method
			 */
			try {
				if (in1_sorted == false) {
					this.am1 = new Sort(in1, (short) len_in1, s1_sizes, am1, join_col_in1, order, sortFld1Len,
							amt_of_mem);
				} else {
					this.am1 = am1;
				}
				if (in2_sorted == false) {
					this.am2 = new Sort(in2, (short) len_in2, s2_sizes, am2, join_col_in2, order, sortFld2Len,
							amt_of_mem);
				} else {
					this.am2 = am2;
				}
			} catch (SortException e) {
				throw new SortException(e, "Sort-Merge Constructor: sorting for tuple failed");
			}

		
			try {
				tupleR.setHdr((short) len_in1, in1, s1_sizes);
				tupleS.setHdr((short) len_in2, in2, s2_sizes);
				tupleRCopy.setHdr((short) len_in1, in1, s1_sizes);
				tupleSCopy.setHdr((short) len_in2, in2, s2_sizes);
			} catch (IOException e) {
				throw new IOException("Sort-Merge Constructor: Set header method for tuple failed due to IO exception",
						e);
			} catch (InvalidTypeException e) {
				throw new InvalidTypeException(e,
						"Sort-Merge Constructor: Set header method for tuple failed due to Invalid type exception");
			} catch (InvalidTupleSizeException e) {
				throw new InvalidTupleSizeException(e,
						"Sort-Merge Constructor: Set header method for tuple failed due to Invalid tuple size exception");
			}

			// initializing joinTuple and joinTypes
			joinTuple = new Tuple();
			joinTypes = new AttrType[n_out_flds];

			matchSpaceR = new byte[1][MINIBASE_PAGESIZE];
			matchSpaceS = new byte[1][MINIBASE_PAGESIZE];

			innerHeapR = null;
			try {
				innerHeapR = new Heapfile(null);
			} catch (IOException e) {
				throw new IOException(
						"SortMerge Constructor: Creating heapfile R for IoBuf R use failed due to IO exception", e);
			}

			innerHeapS = null;
			try {
				innerHeapS = new Heapfile(null);
			} catch (IOException e) {
				throw new IOException(
						"SortMerge Constructor: Creating heapfile S for IoBuf S use failed due to IO exception", e);
			}

			firstScan = true;
			scanDone = false;
			goodTuple = false;

			try {
				TupleUtils.setup_op_tuple(joinTuple, joinTypes, in1, len_in1, in2, len_in2, s1_sizes, s2_sizes,
						proj_list, n_out_flds);
			} catch (IOException e) {
				throw new IOException("SortMerge Constructor: setup_op_tuple failed due to IO exception", e);
			} catch (TupleUtilsException e) {
				throw new TupleUtilsException(e,
						"SortMerge Constructor: setup_op_tuple failed due to TupleUtilsException");
			}
		}

	} // End of SortMerge constructor

	/*--------------------------------------------------------------------------*/
	/**
	 * Reads a tuple from a stream in a less painful way.
	 */
	private boolean readTuple(Tuple tuple, Iterator tupleStream) throws JoinsException, IndexException, UnknowAttrType,
			TupleUtilsException, InvalidTupleSizeException, InvalidTypeException, PageNotReadException,
			PredEvalException, SortException, LowMemException, UnknownKeyTypeException, IOException, Exception {
		Tuple temp;
		temp = tupleStream.get_next();
		if (temp != null) {
			tuple.tupleCopy(temp);
			return true;
		} else {
			return false;
		}
	} // End of readTuple

	/*--------------------------------------------------------------------------*/
	/**
	 * Return the next joined tuple.
	 * 
	 * @return the joined tuple is returned
	 * @exception IOException               I/O errors
	 * @exception JoinsException            some join exception
	 * @exception IndexException            exception from super class
	 * @exception InvalidTupleSizeException invalid tuple size
	 * @exception InvalidTypeException      tuple type not valid
	 * @exception PageNotReadException      exception from lower layer
	 * @exception TupleUtilsException       exception from using tuple utilities
	 * @exception PredEvalException         exception from PredEval class
	 * @exception SortException             sort exception
	 * @exception LowMemException           memory error
	 * @exception UnknowAttrType            attribute type unknown
	 * @exception UnknownKeyTypeException   key type unknown
	 * @exception Exception                 other exceptions
	 */

	public Tuple get_next() throws IOException, JoinsException, IndexException, InvalidTupleSizeException,
			InvalidTypeException, PageNotReadException, TupleUtilsException, PredEvalException, SortException,
			LowMemException, UnknowAttrType, UnknownKeyTypeException, Exception {

		/*
		 * iterate through am1 and am2 to get the tuple using readTuple method above
		 * compare am1 and am2 to find matching join column value go through the while
		 * loop until the entire scan from R and S is not done
		 */

		int compareStatus; // integer returned from comparison of tuple R and tuple S
		while (true) {
			if (goodTuple == false) {
				goodTuple = true;

				// get the first tuple R and S from am1 and am2 for the first scan
				if (firstScan == true) {
					// System.out.println("inside first scan");
					try {
						if (!readTuple(tupleR, this.am1)) {
							return null;
							// tupleR.print(in1);
						}

						if (!readTuple(tupleS, this.am2)) {
							return null;
							// tupleS.print(in2);
						}
						firstScan = false; // firstScan completed
					} catch (JoinsException e) {
						throw new JoinsException(e, "SortMerge get_next(): readTuple failed due to JoinsException");
					} catch (IndexException e) {
						throw new IndexException(e, "SortMerge get_next(): readTuple failed due to JoinsException");
					}
				}
				if (scanDone == true) {
					// System.out.println("inside scan done condition");
					// for the iteration to keep on going
					firstScan = true;
					scanDone = false;
					return null;
				}

				// comparing tupleR with tupleS
				// compareStatus return 0 if tupleR = tupleS when order is ascending else return
				// 1
				// compareStatus returns -1 if tupleR < tupleS when order is ascending
				// else return 1
				// and compareStatus return 1 if tupleR > tupleS when order is ascending else
				// return -1

				try {
					compareStatus = TupleUtils.CompareTupleWithTuple(in1[join_col_in1 - 1], tupleR, join_col_in1,
							tupleS, join_col_in2);
				}

				catch (UnknowAttrType e) {
					throw new UnknowAttrType(e,
							"SortMerge get_next: error during comparison due to unknown attribute type");
				}

				catch (TupleUtilsException e) {
					throw new TupleUtilsException(e,
							"SortMerge get_next: error during comparison of tupleR with tupleS");
				}

				// System.out.println("comparing tuples r and s start");
				while ((compareStatus == -1 && order.tupleOrder == TupleOrder.Ascending)
						|| (compareStatus == 1 && order.tupleOrder == TupleOrder.Descending)) {
					if (!readTuple(tupleR, am1)) {
						return null;
					}
					try {
						compareStatus = TupleUtils.CompareTupleWithTuple(in1[join_col_in1 - 1], tupleR, join_col_in1,
								tupleS, join_col_in2);
					}

					catch (UnknowAttrType e) {
						throw new UnknowAttrType(e,
								"SortMerge get_next: error during comparison due to unknown attribute type");
					}

					catch (TupleUtilsException e) {
						throw new TupleUtilsException(e,
								"SortMerge get_next: error during comparison of tupleR with tupleS");

					}
				}

				while ((compareStatus == 1 && order.tupleOrder == TupleOrder.Ascending)
						|| (compareStatus == -1 && order.tupleOrder == TupleOrder.Descending)) {

					if (!readTuple(tupleS, am2)) {
						return null;
					}
					try {
						compareStatus = TupleUtils.CompareTupleWithTuple(in1[join_col_in1 - 1], tupleR, join_col_in1,
								tupleS, join_col_in2);
					} catch (TupleUtilsException e) {
						throw new TupleUtilsException(e,
								"SortMerge get_next: error during comparison of tupleR with tupleS");
					} catch (UnknowAttrType e) {

						throw new UnknowAttrType(e,
								"SortMerge get_next: error during comparison due to unknown attribute type");
					}

				}

				// there are matches available for above R and S tuples
				if (compareStatus != 0) {
					goodTuple = false; // no join tuple available for given R and S tuples
					continue;
				}

				// copy tuples save current tuple R and S and using next() iterate heap file
				tupleRCopy.tupleCopy(tupleR);
				// tupleRCopy.print(in1);
				tupleSCopy.tupleCopy(tupleS);
				// tupleSCopy.print(in2);

				// clearing up ioBufs, also for re-using ioBuf's
				ioBufR.init(matchSpaceR, 1, tupleR.size(), innerHeapR);
				ioBufS.init(matchSpaceS, 1, tupleS.size(), innerHeapS);

				// get same value and save to io_buf
				// System.out.println("starting to go into iobufR");

				try {
					while (TupleUtils.CompareTupleWithTuple(in1[join_col_in1 - 1], tupleR, join_col_in1, tupleRCopy,
							join_col_in1) == 0) {
						try {
							// insert tupleR into ioBufR
							ioBufR.Put(tupleR);
						} catch (IOException e) {
							throw new IOException("SortMerge get_next: IoBufR error during put", e);
						}
						if (!readTuple(tupleR, am1)) {
							// increment tupleR until match is not found and until the entire scan is not
							// done
							scanDone = true;
							break;
						}
					}
				}

				catch (UnknowAttrType e) {
					throw new UnknowAttrType(e,
							"SortMerge get_next: error during comparison due to unknown attribute type");
				} catch (TupleUtilsException e) {
					throw new TupleUtilsException(e,
							"SortMerge get_next: error during comparison of tupleR with tupleRCopy");
				}

				try {
					// System.out.println("starting to go into iobufS");
					while (TupleUtils.CompareTupleWithTuple(in1[join_col_in1 - 1], tupleS, join_col_in2, tupleSCopy,
							join_col_in2) == 0) {
						try {
							// insert tupleS into ioBufS
							ioBufS.Put(tupleS);

						} catch (IOException e) {
							throw new IOException("SortMerge get_next: IoBufS error during put", e);
						}
						if (!readTuple(tupleS, am2)) {
							// increment tupleS until match is not found and until the entire scan is not
							// done
							scanDone = true;
							break;
						}
					}
				}

				catch (UnknowAttrType e) {
					throw new UnknowAttrType(e,
							"SortMerge get_next: error during comparison due to unknown attribute type");

				} catch (TupleUtilsException e) {
					throw new TupleUtilsException(e,
							"SortMerge get_next: error during comparison of tupleS with tupleSCopy");
				}

			} // End of goodTuple condition

			// joining/merging begins

			// checking iobuf's for if either one of them is empty or not
			// and then getting tuple from ioBufS IF NOT EMPTY
			// System.out.println("checking ioBufS " + ioBufS.flush());

			if (ioBufS.Get(tupleSCopy) == null) {
				if (ioBufR.Get(tupleRCopy) == null) {
					goodTuple = false;
					continue;
				} else {
					ioBufS.reread();
					ioBufS.Get(tupleSCopy);
				}
			}

			// Join the OUTER tuple and the INNER.
			// That is, if the predicates of the query are true.
			// check if copies of tupleR and tupleS can join or not
			// if they can, then we merge/join them together to get out joinTuple

			try {
				if (PredEval.Eval(outFilter, tupleRCopy, tupleSCopy, in1, in2) == true) {
					try {
						Projection.Join(tupleRCopy, in1, tupleSCopy, in2, joinTuple, proj_list, n_out_flds);

						goodTuple = true;
						return joinTuple;
						
					} catch (UnknowAttrType e) {
						throw new UnknowAttrType(e,
								"SortMerge get_next: error during join due to unknown attribute type");
						
					} catch (FieldNumberOutOfBoundException e) {
						throw new FieldNumberOutOfBoundException(e,
								"SortMerge get_next: error during join due to field number out of bound");
					}

				}
			} catch (PredEvalException e) {
				throw new PredEvalException(e, "SortMerge get_next: error during computation of PredEval");
			}
		}

	}// End of get_next()

	/*--------------------------------------------------------------------------*/
	/**
	 * implement the abstract method close() from super class Iterator to finish
	 * cleaning up
	 * 
	 * @exception IOException    I/O error from lower layers
	 * @exception JoinsException join error from lower layers
	 * @exception IndexException index access error
	 */

	public void close() throws JoinsException, IOException {

		if (!closeFlag) {

			try {
				this.am1.close();
				this.am2.close();
			} catch (Exception e) {
				throw new JoinsException(e, "SortMerge close: some join exception : error in closing iterator.");
			}

			if (innerHeapR != null && innerHeapS != null) {
				try {
					innerHeapR.deleteFile();
					innerHeapS.deleteFile();
				} catch (Exception e) {
					// catch exceptions thrown by deleteFile
				}
				innerHeapR = null;
				innerHeapS = null;
			}

			closeFlag = true;
		}
	} // End of close

} // End of CLASS SortMerge
