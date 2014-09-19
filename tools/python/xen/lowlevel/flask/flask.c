/******************************************************************************
 * flask.c
 * 
 * Authors: George Coker, <gscoker@alpha.ncsc.mil>
 *          Michael LeMay, <mdlemay@epoch.ncsc.mil>
 *
 *
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License version 2,
 *    as published by the Free Software Foundation.
 */

#include <Python.h>
#include <xenctrl.h>
#include <flask.h>

#define PKG "xen.lowlevel.flask"
#define CLS "flask"

#define CTX_LEN 1024

static PyObject *xc_error_obj;

typedef struct {
    PyObject_HEAD;
    int xc_handle;
} XcObject;

static PyObject *pyflask_context_to_sid(PyObject *self, PyObject *args,
                                                                 PyObject *kwds)
{
    int xc_handle;
    char *ctx;
    char *buf;
    uint32_t len;
    uint32_t sid;
    int ret;

    static char *kwd_list[] = { "context", NULL };

    if ( !PyArg_ParseTupleAndKeywords(args, kwds, "s", kwd_list,
                                      &ctx) )
        return NULL;

    len = strlen(ctx);

    buf = malloc(len);
    if (!buf) {
        errno = -ENOMEM;
        PyErr_SetFromErrno(xc_error_obj);
    }
    
    memcpy(buf, ctx, len);
    
    xc_handle = xc_interface_open();
    if (xc_handle < 0) {
        errno = xc_handle;
        return PyErr_SetFromErrno(xc_error_obj);
    }
    
    ret = flask_context_to_sid(xc_handle, buf, len, &sid);
        
    xc_interface_close(xc_handle);

    free(buf);
    
    if ( ret != 0 ) {
        errno = -ret;
        return PyErr_SetFromErrno(xc_error_obj);
    }

    return PyInt_FromLong(sid);
}

static PyObject *pyflask_sid_to_context(PyObject *self, PyObject *args,
                                                                 PyObject *kwds)
{
    int xc_handle;
    uint32_t sid;
    char ctx[CTX_LEN];
    uint32_t ctx_len = CTX_LEN;
    int ret;

    static char *kwd_list[] = { "sid", NULL };

    if ( !PyArg_ParseTupleAndKeywords(args, kwds, "i", kwd_list,
                                      &sid) )
        return NULL;

    xc_handle = xc_interface_open();
    if (xc_handle < 0) {
        errno = xc_handle;
        return PyErr_SetFromErrno(xc_error_obj);
    }
    
    ret = flask_sid_to_context(xc_handle, sid, ctx, ctx_len);
    
    xc_interface_close(xc_handle);
    
    if ( ret != 0 ) {
        errno = -ret;
        return PyErr_SetFromErrno(xc_error_obj);
    }

    return Py_BuildValue("s", ctx, ctx_len);
}


static PyMethodDef pyflask_methods[] = {
    { "flask_context_to_sid",
      (PyCFunction)pyflask_context_to_sid,
      METH_KEYWORDS, "\n"
      "Convert a context string to a dynamic SID.\n"
      " context [str]: String specifying context to be converted\n"
      "Returns: [int]: Numeric SID on success; -1 on error.\n" },

    { "flask_sid_to_context",
      (PyCFunction)pyflask_sid_to_context,
      METH_KEYWORDS, "\n"
      "Convert a dynamic SID to context string.\n"
      " context [int]: SID to be converted\n"
      "Returns: [str]: Numeric SID on success; -1 on error.\n" },

    { NULL, NULL, 0, NULL }
};

PyMODINIT_FUNC initflask(void)
{
    Py_InitModule("flask", pyflask_methods);
}


/*
 * Local variables:
 *  c-indent-level: 4
 *  c-basic-offset: 4
 * End:
 */
