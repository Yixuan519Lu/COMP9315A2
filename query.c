// query.c ... query scan functions
// part of Multi-attribute Linear-hashed Files
// Manage creating and using Query objects
// Last modified by John Shepherd, July 2019



// discussed the code logic with Jin and Yijin
#include "defs.h"
#include "query.h"
#include "reln.h"
#include "tuple.h"
#include "hash.h"

// A suggestion ... you can change however you like

struct QueryRep
{
	Reln rel;		// need to remember Relation info
	Bits known;		// the hash value from MAH
	Bits unknown;	// the unknown bits from MAH
	PageID curpage; // current page in scan
	int is_ovflow;	// are we in the overflow pages?
	Offset curtup;	// offset of current tuple within page
	Bits startPGID;
	Tuple queryString;
	int depth;
	int curCombination;
	Count numVisitedTp; 
};

Query startQuery(Reln r, char *q)
{
	Query new = malloc(sizeof(struct QueryRep));
	assert(new != NULL);
	Bits known = 0;	  // the hash value from MAH
	Bits unknown = 0; // the unknown bits from MAH
	new->depth = depth(r);
	Count nvals = nattrs(r);
	char *queryString = q;
	char **queryAttList = malloc(nvals * sizeof(char *));
	size_t lenQString = strlen(queryString);
	ChVecItem *cv = chvec(r);
	Bits hashBits[nvals];
	Bits mask = 0; // the binary representation of the corresponding mask
	Bits startPGID = 0;
	for (int i = 0; i < depth(r); i++)
	{
		mask = setBit(mask, i);
	}
	for (int i = 0; i < nvals; i++, queryString++)
	{
		int j = 0;
		queryAttList[i] = malloc((lenQString + 1) * sizeof(char)); // raw hash
		while (*queryString != '\0' && *queryString != ',')
		{
			queryAttList[i][j] = *queryString;
			queryString++;
			j++;
		}
		queryAttList[i][j] = '\0';
		queryAttList[i] = realloc(queryAttList[i], sizeof(char) * (j + 1));
	}
	for (int i = 0; i < nvals; i++)
	{
		hashBits[i] = hash_any((unsigned char *)queryAttList[i], strlen(queryAttList[i]));
	}
	// Builds the partial hash value
	for (int i = 0; i < nvals; i++)
	{
		if (*queryAttList[i] != '?')
		{
			int curAtt, curBit;
			for (int j = 0; j < MAXBITS; j++)
			{
				curAtt = cv[j].att;
				curBit = cv[j].bit;
				if (curAtt == i && bitIsSet(hashBits[curAtt], curBit))
				{
					known = setBit(known, j);
				}
			}
		}
		else
		{
			int curAtt;
			for (int j = 0; j < MAXBITS; j++)
			{
				curAtt = cv[j].att;\
				if (curAtt == i)
				{
					unknown = setBit(unknown, j);
				}
			}
		}
	}
	// perform a bitwise AND operation between the known bits and the mask
	startPGID = known & mask;
	if (startPGID < splitp(r))
	{
		startPGID = known & setBit(mask, depth(r));
		new->depth += 1;
	}
	// startPGID = (startPGID < splitp(r)) ? setBit(mask, depth(r)) & known : startPGID;
	// new->depth += (startPGID < splitp(r)) ? 1 : 0;
	new->startPGID = startPGID;
	new->known = known;
	new->unknown = unknown;
	new->rel = r;
	new->curpage = 0;
	new->curtup = 0;
	new->is_ovflow = 0;
	new->curCombination = 0;
	new->numVisitedTp = 0;
	new->queryString = q;

	// //test
	//  char testKnown[MAXBITS+1];
	//  bitsString(known,testKnown);
	//  printf("KNOWN:  %s\n",testKnown);
	// printf("KNOWN: %u\n",new->known);
	//  char testUnknown[MAXBITS+1];
	//  bitsString(unknown,testUnknown);
	//  printf("UNKNOWN:%s\n",testUnknown);
	// printf("UNKNOWN: %u\n",new->unknown);
	return new;
}
void resetQueryState(Query q,int of,Offset pid) {
    q->curtup = 0;
    q->numVisitedTp = 0;
    q->is_ovflow = of;
	q->curpage = pid;
}
int getNumUnknown(Query q){
	int numUnknown = 0;
	for (int i = 0; i < MAXBITS - 1; i++)
	{   
        if (i>q->depth-1){
            break;
        }
		if (bitIsSet(q->unknown, i)==1){
			numUnknown++;
		}
	}
	//printf("getNumUnknown:  %d\n",numUnknown);
	return numUnknown;
}

// Calculate the next combination mask based on unknown bits and the current combination counter
Bits calculateNextMask(Bits unknown, int numUnknown, Bits currentCombination) {
    Bits mask = 0;
	int nextPos=0;
    for (int i = 0; i < numUnknown; i++) {
        while (!(setBit(0, nextPos) & unknown)) {
            nextPos++;  // Skip non-unknown bits
        }
        if (setBit(0, i) & currentCombination) {
            mask = setBit(mask, nextPos);  // Set this position in the mask
        }
        nextPos++;  // Move to the next position
    }
    return mask;
}
Tuple getNextTuple(Query q)
{
	//traverse starting from current tuple, if we do not find target, check if there exits ofpage. traverse all ofpages. jump to next page.
	while (TRUE)
	{
		FILE *f;
		if(q->is_ovflow){
			f=ovflowFile(q->rel);
		}else{
			f=dataFile(q->rel);
		}
		Page currPG = getPage(f, q->curpage);
		Count Ntuple = pageNTuples(currPG);	
		if (q->numVisitedTp < Ntuple){
			//printf("curpage:  %d  isoverflow: %d\n", q->curpage,q->is_ovflow);
			Tuple next;
			while (q->numVisitedTp < Ntuple)
			{
				next = copyString(pageData(currPG) + q->curtup);
				q->curtup += strlen(next) + 1;
				q->numVisitedTp += 1;
				//printf("maxtuple: %d tuple: %d curpage:  %d  isoverflow: %d  matched: %s\n",Ntuple,q->numVisitedTp, q->curpage,q->is_ovflow,next);
				// printf("ctuple:  %s\n",next);
				if (tupleMatch(q->rel, q->queryString, next))
				{
					//printf("maxtuple: %d tuple: %d curpage:  %d  isoverflow: %d  matched: %s\n",Ntuple,q->numVisitedTp, q->curpage,q->is_ovflow,next);
					if (next != NULL)
						return next;
				}
				else{
					free(next);
				}
			}
		}
		else if (pageOvflow(currPG) == NO_PAGE)
		{
			int numUnknown = getNumUnknown(q);
			int totalCombinations = 1 << numUnknown;
			if (++q->curCombination >= totalCombinations) {
 			   break;
			}
			Bits mask = calculateNextMask(q->unknown, numUnknown, q->curCombination);
			// Update the query's current page and state based on the calculated mask and other parameters
			Bits curpage = q->startPGID | mask;
			if (curpage < npages(q->rel)) {
				resetQueryState(q,0,curpage);
			}
			else {	
				break;
			}
		}
		else if (pageOvflow(currPG) != NO_PAGE)
		{
			resetQueryState(q,1,pageOvflow(currPG));
		}
		else{
			continue;
		}
	}	
	return NULL;
}

// clean up a QueryRep object and associated data

void closeQuery(Query q)
{
	free(q);
}
