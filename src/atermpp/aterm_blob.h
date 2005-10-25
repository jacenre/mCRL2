// ======================================================================
//
// Copyright (c) 2004, 2005 Wieger Wesselink
//
// ----------------------------------------------------------------------
//
// file          : atermpp/aterm_blob.h
// date          : 25-10-2005
// version       : 1.0
//
// author(s)     : Wieger Wesselink  <J.W.Wesselink@tue.nl>
//
// ======================================================================

#ifndef ATERM_BLOB_H
#define ATERM_BLOB_H

/** @file
  * This is a C++ wrapper around the ATerm library.
  */

#include "atermpp/aterm.h"

namespace atermpp
{
  //---------------------------------------------------------//
  //                     aterm_blob
  //---------------------------------------------------------//
  class aterm_blob: public aterm
  {
   public:
      aterm_blob(ATermBlob t)
        : aterm(t)
      {}

      aterm_blob(ATerm t)
        : aterm(t)
      {
        assert(type() == AT_BLOB);
      }

      /**
        * Build a Binary Large OBject given size (in bytes) and data.
        * This function can be used to create an aterm of type blob, holding the data
        * pointed to by data. No copy of this data area is made, so the user should allocate this himself.
        *    Note:  due to the internal representation of a blob, size cannot exceed 224 in the current
        * implementation. This limits the size of the data area to 16 Mb.
        **/
      aterm_blob(unsigned int size, void* data)
        : aterm(ATmakeBlob(size, data))
      {}

      /**
        * Get the data section of the blob.
        **/
      void* data()
      {
        return ATgetBlobData(void2blob(m_term));
      }

      /**
        * Get the size (in bytes) of the blob.
        **/
      unsigned int size() const
      {
        return ATgetBlobSize(void2blob(m_term));
      }
  };
  
} // namespace atermpp

#endif // ATERM_BLOB_H
