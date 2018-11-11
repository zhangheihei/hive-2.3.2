/**
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.hadoop.hive.metastore;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.hive.metastore.hooks.JDOConnectionURLHook;

/**
 *
 * DummyJdoConnectionUrlHook.
 *
 * An implementation of JDOConnectionURLHook which simply returns CORRECT_URL when
 * getJdoConnectionUrl is called.
 */
public class DummyJdoConnectionUrlHook implements JDOConnectionURLHook {

  public static final String initialUrl = "BAD_URL";
  public static final String newUrl = "CORRECT_URL";

  @Override
  public String getJdoConnectionUrl(Configuration conf) throws Exception {
    return newUrl;
  }

  @Override
  public void notifyBadConnectionUrl(String url) {
  }

}
