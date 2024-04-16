// reln.c ... functions on Relations
// part of Multi-attribute Linear-hashed Files
// Last modified by John Shepherd, July 2019

// discussed the code logic with Jin and Yijin

#include "defs.h"
#include "reln.h"
#include "page.h"
#include "tuple.h"
#include "chvec.h"
#include "bits.h"
#include "hash.h"

#define HEADERSIZE (3 * sizeof(Count) + sizeof(Offset))

struct RelnRep
{
	Count nattrs; // number of attributes
	Count depth;  // depth of main data file
	Offset sp;	  // split pointer
	Count npages; // number of main data pages
	Count ntups;  // total number of tuples
	ChVec cv;	  // choice vector
	char mode;	  // open for read/write
	FILE *info;	  // handle on info file
	FILE *data;	  // handle on data file
	FILE *ovflow; // handle on ovflow file
};

// create a new relation (three files)

Status newRelation(char *name, Count nattrs, Count npages, Count d, char *cv)
{
	char fname[MAXFILENAME];
	Reln r = malloc(sizeof(struct RelnRep));
	r->nattrs = nattrs;
	r->depth = d;
	r->sp = 0;
	r->npages = npages;
	r->ntups = 0;
	r->mode = 'w';
	assert(r != NULL);
	if (parseChVec(r, cv, r->cv) != OK)
		return ~OK;
	sprintf(fname, "%s.info", name);
	r->info = fopen(fname, "w");
	assert(r->info != NULL);
	sprintf(fname, "%s.data", name);
	r->data = fopen(fname, "w");
	assert(r->data != NULL);
	sprintf(fname, "%s.ovflow", name);
	r->ovflow = fopen(fname, "w");
	assert(r->ovflow != NULL);
	int i;
	for (i = 0; i < npages; i++)
		addPage(r->data);
	closeRelation(r);
	return 0;
}

// check whether a relation already exists

Bool existsRelation(char *name)
{
	char fname[MAXFILENAME];
	sprintf(fname, "%s.info", name);
	FILE *f = fopen(fname, "r");
	if (f == NULL)
		return FALSE;
	else
	{
		fclose(f);
		return TRUE;
	}
}

// set up a relation descriptor from relation name
// open files, reads information from rel.info

Reln openRelation(char *name, char *mode)
{
	Reln r;
	r = malloc(sizeof(struct RelnRep));
	assert(r != NULL);
	char fname[MAXFILENAME];
	sprintf(fname, "%s.info", name);
	r->info = fopen(fname, mode);
	assert(r->info != NULL);
	sprintf(fname, "%s.data", name);
	r->data = fopen(fname, mode);
	assert(r->data != NULL);
	sprintf(fname, "%s.ovflow", name);
	r->ovflow = fopen(fname, mode);
	assert(r->ovflow != NULL);
	// Naughty: assumes Count and Offset are the same size
	int n = fread(r, sizeof(Count), 5, r->info);
	assert(n == 5);
	n = fread(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
	assert(n == MAXCHVEC);
	r->mode = (mode[0] == 'w' || mode[1] == '+') ? 'w' : 'r';
	return r;
}

// release files and descriptor for an open relation
// copy latest information to .info file

void closeRelation(Reln r)
{
	// make sure updated global data is put in info
	// Naughty: assumes Count and Offset are the same size
	if (r->mode == 'w')
	{
		fseek(r->info, 0, SEEK_SET);
		// write out core relation info (#attr,#pages,d,sp)
		int n = fwrite(r, sizeof(Count), 5, r->info);
		assert(n == 5);
		// write out choice vector
		n = fwrite(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
		assert(n == MAXCHVEC);
	}
	fclose(r->info);
	fclose(r->data);
	fclose(r->ovflow);
	free(r);
}

PageID handleOverflow(Reln r, Page pg, Tuple t, PageID p,int isSplit)
{
	PageID returnPage = NO_PAGE;
	if (pageOvflow(pg) == NO_PAGE)
	{
		// add first overflow page in chain
		PageID newp = addPage(r->ovflow);
		pageSetOvflow(pg, newp);
		putPage(r->data, p, pg);
		Page newpg = getPage(r->ovflow, newp);
		if (addToPage(newpg, t) == OK)
		{
			if(!isSplit){
				r->ntups++;
			}
			putPage(r->ovflow, newp, newpg);
			returnPage = p;
		}
	}
	else
	{
		// scan overflow chain until we find space
		Page ovpg, prevpg = NULL;
		PageID ovp = pageOvflow(pg), prevp = NO_PAGE;
		while (ovp != NO_PAGE)
		{
			ovpg = getPage(r->ovflow, ovp);
			if (addToPage(ovpg, t) == OK)
			{
				if (prevpg != NULL) free(prevpg);
				putPage(r->ovflow, ovp, ovpg);
				returnPage = p;
				if(!isSplit){
					r->ntups++;
				}
				break;
			}
			else
			{
				prevp = ovp;
				prevpg = ovpg;
				ovp = pageOvflow(ovpg);
			}
		}
		if (returnPage == NO_PAGE && prevpg != NULL)
		{ // all overflow pages are full; add another to chain
			PageID newp = addPage(r->ovflow);
			Page newpg = getPage(r->ovflow, newp);
			if (addToPage(newpg, t) == OK)
			{
				putPage(r->ovflow, newp, newpg);
				pageSetOvflow(prevpg, newp);
				putPage(r->ovflow, prevp, prevpg);
				if(!isSplit){
					r->ntups++;
				}
				returnPage = p;
			}
		}
	}
	return returnPage;
}
void updateSplit(Reln r)
{
	r->sp += 1;
	r->sp = (r->sp == (1 << r->depth)) ? 0 : r->sp;
	r->depth += (r->sp == 0) ? 1 : 0;
}
PageID calculatePageID(Reln r, Bits hash, int isSplit)
{
    if (isSplit)
    {
        return getLower(hash, r->depth + 1);
    }
    else
    {
        if (r->depth == 0)
        {
            return 0;
        }
        
        PageID pageID = getLower(hash, r->depth);
        if (pageID < r->sp)
        {
            pageID = getLower(hash, r->depth + 1);
        }
        return pageID;
    }
}
// Function to insert a tuple into a page and handle potential overflow
PageID insertTupleInPage(Reln r, Tuple tuple, int isSplit)
{
    Bits hash = tupleHash(r, tuple);
    PageID pageID = calculatePageID(r, hash, isSplit);
    Page page = getPage(r->data, pageID);

    if (addToPage(page, tuple) == OK)
    {
        if (!isSplit) {
            r->ntups++;
        }
        putPage(r->data, pageID, page);
        return pageID;
    }
    else
    {
        return handleOverflow(r, page, tuple, pageID, isSplit);
    }
}


PageID addToRelation(Reln r, Tuple t)
{
    PageID returnPage = insertTupleInPage(r, t, 0);
    if (returnPage != NO_PAGE && shouldSplitRelation(r))
    {
        performSplit(r);
    }
    return returnPage;
}

int shouldSplitRelation(Reln r)
{
    return !(r->ntups % (1024 / (10 * r->nattrs)));
}

void performSplit(Reln r)
{
    PageID newPageID = addPage(r->data);
    assert(newPageID != NO_PAGE);
    r->npages += 1;

    Offset nextsp = r->sp;
    Offset curtup = 0;
    while (TRUE)
    {
        Page curPage = getPage(r->data, nextsp);
        if (!pageNTuples(curPage)) break;

        redistributeTuples(r, &nextsp, &curtup, curPage);
        if(nextsp == NO_PAGE) break;
    }

    updateSplit(r);
}

void redistributeTuples(Reln r, Offset* nextsp, Offset* curtup, Page curPage)
{
    Count numVisitedTp = 0;
    Tuple next;
    while (numVisitedTp < pageNTuples(curPage))
    {
        next = copyString(pageData(curPage) + *curtup);
        *curtup += strlen(next) + 1;
        insertTupleInPage(r, next, 1);
        numVisitedTp++;

        if (numVisitedTp >= pageNTuples(curPage))
        {
            *curtup = 0;
            Page splitPage = newPage();
            putPage(r->data, *nextsp, splitPage);
            *nextsp = pageOvflow(curPage);
            if (*nextsp == NO_PAGE) break;
        }
    }
}

FILE *dataFile(Reln r) { return r->data; }
FILE *ovflowFile(Reln r) { return r->ovflow; }
Count nattrs(Reln r) { return r->nattrs; }
Count npages(Reln r) { return r->npages; }
Count ntuples(Reln r) { return r->ntups; }
Count depth(Reln r) { return r->depth; }
Count splitp(Reln r) { return r->sp; }
ChVecItem *chvec(Reln r) { return r->cv; }

// displays info about open Reln

void relationStats(Reln r)
{
	printf("Global Info:\n");
	printf("#attrs:%d  #pages:%d  #tuples:%d  d:%d  sp:%d\n",
		   r->nattrs, r->npages, r->ntups, r->depth, r->sp);
	printf("Choice vector\n");
	printChVec(r->cv);
	printf("Bucket Info:\n");
	printf("%-4s %s\n", "#", "Info on pages in bucket");
	printf("%-4s %s\n", "", "(pageID,#tuples,freebytes,ovflow)");
	for (Offset pid = 0; pid < r->npages; pid++)
	{
		printf("[%2d]  ", pid);
		Page p = getPage(r->data, pid);
		Count ntups = pageNTuples(p);
		Count space = pageFreeSpace(p);
		Offset ovid = pageOvflow(p);
		printf("(d%d,%d,%d,%d)", pid, ntups, space, ovid);
		free(p);
		while (ovid != NO_PAGE)
		{
			Offset curid = ovid;
			p = getPage(r->ovflow, ovid);
			ntups = pageNTuples(p);
			space = pageFreeSpace(p);
			ovid = pageOvflow(p);
			printf(" -> (ov%d,%d,%d,%d)", curid, ntups, space, ovid);
			free(p);
		}
		putchar('\n');
	}
}

